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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1080_, lean_object* v___x_1081_, lean_object* v_inst_1082_, lean_object* v_f_1083_, lean_object* v_toBind_1084_, lean_object* v_a_1085_, lean_object* v_x_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1080_, v___x_1081_, v_inst_1082_, v_f_1083_, v_toBind_1084_, v_a_1085_, v_x_1086_, v___y_1087_);
lean_dec_ref(v_a_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1089_, lean_object* v_f_1090_, lean_object* v_n_1091_, lean_object* v_b_1092_){
_start:
{
if (lean_obj_tag(v_n_1091_) == 0)
{
lean_object* v_toApplicative_1093_; lean_object* v_toBind_1094_; lean_object* v_toPure_1095_; lean_object* v_cs_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_toApplicative_1093_ = lean_ctor_get(v_inst_1089_, 0);
v_toBind_1094_ = lean_ctor_get(v_inst_1089_, 1);
lean_inc_n(v_toBind_1094_, 2);
v_toPure_1095_ = lean_ctor_get(v_toApplicative_1093_, 1);
v_cs_1096_ = lean_ctor_get(v_n_1091_, 0);
lean_inc_n(v_toPure_1095_, 2);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1097_, 0, v_toPure_1095_);
v___x_1098_ = lean_box(0);
lean_inc_ref(v_inst_1089_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1099_, 0, v_toPure_1095_);
lean_closure_set(v___f_1099_, 1, v___x_1098_);
lean_closure_set(v___f_1099_, 2, v_inst_1089_);
lean_closure_set(v___f_1099_, 3, v_f_1090_);
lean_closure_set(v___f_1099_, 4, v_toBind_1094_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v_b_1092_);
v_sz_1101_ = lean_array_size(v_cs_1096_);
v___x_1102_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1096_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1089_, v_cs_1096_, v___f_1099_, v_sz_1101_, v___x_1102_, v___x_1100_);
v___x_1104_ = lean_apply_4(v_toBind_1094_, lean_box(0), lean_box(0), v___x_1103_, v___f_1097_);
return v___x_1104_;
}
else
{
lean_object* v_toApplicative_1105_; lean_object* v_toBind_1106_; lean_object* v_toPure_1107_; lean_object* v_vs_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_toApplicative_1105_ = lean_ctor_get(v_inst_1089_, 0);
v_toBind_1106_ = lean_ctor_get(v_inst_1089_, 1);
lean_inc_n(v_toBind_1106_, 2);
v_toPure_1107_ = lean_ctor_get(v_toApplicative_1105_, 1);
v_vs_1108_ = lean_ctor_get(v_n_1091_, 0);
lean_inc_n(v_toPure_1107_, 2);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1109_, 0, v_toPure_1107_);
v___x_1110_ = lean_box(0);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1111_, 0, v_toPure_1107_);
lean_closure_set(v___f_1111_, 1, v___x_1110_);
lean_closure_set(v___f_1111_, 2, v_f_1090_);
lean_closure_set(v___f_1111_, 3, v_toBind_1106_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v_b_1092_);
v_sz_1113_ = lean_array_size(v_vs_1108_);
v___x_1114_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1108_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1089_, v_vs_1108_, v___f_1111_, v_sz_1113_, v___x_1114_, v___x_1112_);
v___x_1116_ = lean_apply_4(v_toBind_1106_, lean_box(0), lean_box(0), v___x_1115_, v___f_1109_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1117_, lean_object* v___x_1118_, lean_object* v_inst_1119_, lean_object* v_f_1120_, lean_object* v_toBind_1121_, lean_object* v_a_1122_, lean_object* v_x_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_snd_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_snd_1125_ = lean_ctor_get(v___y_1124_, 1);
lean_inc_n(v_snd_1125_, 2);
lean_dec_ref(v___y_1124_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1126_, 0, v_snd_1125_);
lean_closure_set(v___f_1126_, 1, v_toPure_1117_);
lean_closure_set(v___f_1126_, 2, v___x_1118_);
v___x_1127_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1119_, v_f_1120_, v_a_1122_, v_snd_1125_);
v___x_1128_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v___x_1127_, v___f_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1129_, lean_object* v_f_1130_, lean_object* v_n_1131_, lean_object* v_b_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1129_, v_f_1130_, v_n_1131_, v_b_1132_);
lean_dec_ref(v_n_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inh_1138_, lean_object* v_f_1139_, lean_object* v_n_1140_, lean_object* v_b_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1137_, v_f_1139_, v_n_1140_, v_b_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_m_1145_, lean_object* v_inst_1146_, lean_object* v_inh_1147_, lean_object* v_f_1148_, lean_object* v_n_1149_, lean_object* v_b_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1143_, v_00_u03b2_1144_, v_m_1145_, v_inst_1146_, v_inh_1147_, v_f_1148_, v_n_1149_, v_b_1150_);
lean_dec_ref(v_n_1149_);
lean_dec(v_inh_1147_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1152_, lean_object* v_____s_1153_){
_start:
{
lean_object* v_fst_1154_; 
v_fst_1154_ = lean_ctor_get(v_____s_1153_, 0);
if (lean_obj_tag(v_fst_1154_) == 0)
{
lean_object* v_snd_1155_; lean_object* v___x_1156_; 
v_snd_1155_ = lean_ctor_get(v_____s_1153_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v_____s_1153_);
v___x_1156_ = lean_apply_2(v_toPure_1152_, lean_box(0), v_snd_1155_);
return v___x_1156_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1158_; 
lean_inc_ref(v_fst_1154_);
lean_dec_ref(v_____s_1153_);
v_val_1157_ = lean_ctor_get(v_fst_1154_, 0);
lean_inc(v_val_1157_);
lean_dec_ref(v_fst_1154_);
v___x_1158_ = lean_apply_2(v_toPure_1152_, lean_box(0), v_val_1157_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1159_, lean_object* v_toPure_1160_, lean_object* v___x_1161_, lean_object* v_____do__lift_1162_){
_start:
{
if (lean_obj_tag(v_____do__lift_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v___x_1161_);
v_a_1163_ = lean_ctor_get(v_____do__lift_1162_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_____do__lift_1162_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1165_ = v_____do__lift_1162_;
v_isShared_1166_ = v_isSharedCheck_1173_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v_____do__lift_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1173_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1163_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v_snd_1159_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_apply_2(v_toPure_1160_, lean_box(0), v___x_1170_);
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_snd_1159_);
v_a_1174_ = lean_ctor_get(v_____do__lift_1162_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_____do__lift_1162_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1176_ = v_____do__lift_1162_;
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v_____do__lift_1162_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1161_);
lean_ctor_set(v___x_1178_, 1, v_a_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_apply_2(v_toPure_1160_, lean_box(0), v___x_1180_);
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1184_, lean_object* v___x_1185_, lean_object* v_f_1186_, lean_object* v_toBind_1187_, lean_object* v_a_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_snd_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_snd_1191_ = lean_ctor_get(v___y_1190_, 1);
lean_inc_n(v_snd_1191_, 2);
lean_dec_ref(v___y_1190_);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1192_, 0, v_snd_1191_);
lean_closure_set(v___f_1192_, 1, v_toPure_1184_);
lean_closure_set(v___f_1192_, 2, v___x_1185_);
v___x_1193_ = lean_apply_2(v_f_1186_, v_a_1188_, v_snd_1191_);
v___x_1194_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1193_, v___f_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1195_, lean_object* v_f_1196_, lean_object* v_toBind_1197_, lean_object* v_tail_1198_, lean_object* v_inst_1199_, lean_object* v___f_1200_, lean_object* v_____do__lift_1201_){
_start:
{
if (lean_obj_tag(v_____do__lift_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1203_; 
lean_dec(v___f_1200_);
lean_dec_ref(v_inst_1199_);
lean_dec_ref(v_tail_1198_);
lean_dec(v_toBind_1197_);
lean_dec(v_f_1196_);
v_a_1202_ = lean_ctor_get(v_____do__lift_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v_____do__lift_1201_);
v___x_1203_ = lean_apply_2(v_toPure_1195_, lean_box(0), v_a_1202_);
return v___x_1203_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1204_ = lean_ctor_get(v_____do__lift_1201_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v_____do__lift_1201_);
v___x_1205_ = lean_box(0);
lean_inc(v_toBind_1197_);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1206_, 0, v_toPure_1195_);
lean_closure_set(v___f_1206_, 1, v___x_1205_);
lean_closure_set(v___f_1206_, 2, v_f_1196_);
lean_closure_set(v___f_1206_, 3, v_toBind_1197_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v_a_1204_);
v_sz_1208_ = lean_array_size(v_tail_1198_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1199_, v_tail_1198_, v___f_1206_, v_sz_1208_, v___x_1209_, v___x_1207_);
v___x_1211_ = lean_apply_4(v_toBind_1197_, lean_box(0), lean_box(0), v___x_1210_, v___f_1200_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1212_, lean_object* v_t_1213_, lean_object* v_init_1214_, lean_object* v_f_1215_){
_start:
{
lean_object* v_toApplicative_1216_; lean_object* v_toBind_1217_; lean_object* v_root_1218_; lean_object* v_tail_1219_; lean_object* v_toPure_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; 
v_toApplicative_1216_ = lean_ctor_get(v_inst_1212_, 0);
v_toBind_1217_ = lean_ctor_get(v_inst_1212_, 1);
lean_inc_n(v_toBind_1217_, 2);
v_root_1218_ = lean_ctor_get(v_t_1213_, 0);
v_tail_1219_ = lean_ctor_get(v_t_1213_, 1);
v_toPure_1220_ = lean_ctor_get(v_toApplicative_1216_, 1);
lean_inc_n(v_toPure_1220_, 2);
lean_inc(v_f_1215_);
lean_inc_ref(v_inst_1212_);
v___x_1221_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1212_, v_f_1215_, v_root_1218_, v_init_1214_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1222_, 0, v_toPure_1220_);
lean_inc_ref(v_tail_1219_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1223_, 0, v_toPure_1220_);
lean_closure_set(v___f_1223_, 1, v_f_1215_);
lean_closure_set(v___f_1223_, 2, v_toBind_1217_);
lean_closure_set(v___f_1223_, 3, v_tail_1219_);
lean_closure_set(v___f_1223_, 4, v_inst_1212_);
lean_closure_set(v___f_1223_, 5, v___f_1222_);
v___x_1224_ = lean_apply_4(v_toBind_1217_, lean_box(0), lean_box(0), v___x_1221_, v___f_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1225_, lean_object* v_t_1226_, lean_object* v_init_1227_, lean_object* v_f_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1225_, v_t_1226_, v_init_1227_, v_f_1228_);
lean_dec_ref(v_t_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1230_, lean_object* v_m_1231_, lean_object* v_inst_1232_, lean_object* v_00_u03b2_1233_, lean_object* v_t_1234_, lean_object* v_init_1235_, lean_object* v_f_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1232_, v_t_1234_, v_init_1235_, v_f_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_m_1239_, lean_object* v_inst_1240_, lean_object* v_00_u03b2_1241_, lean_object* v_t_1242_, lean_object* v_init_1243_, lean_object* v_f_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1238_, v_m_1239_, v_inst_1240_, v_00_u03b2_1241_, v_t_1242_, v_init_1243_, v_f_1244_);
lean_dec_ref(v_t_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1247_, 0, lean_box(0));
lean_closure_set(v___x_1247_, 1, lean_box(0));
lean_closure_set(v___x_1247_, 2, v_inst_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1248_, lean_object* v_m_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1251_, 0, lean_box(0));
lean_closure_set(v___x_1251_, 1, lean_box(0));
lean_closure_set(v___x_1251_, 2, v_inst_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1252_, lean_object* v_____s_1253_){
_start:
{
lean_object* v_fst_1254_; 
v_fst_1254_ = lean_ctor_get(v_____s_1253_, 0);
lean_inc(v_fst_1254_);
lean_dec_ref(v_____s_1253_);
if (lean_obj_tag(v_fst_1254_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_apply_2(v_toPure_1252_, lean_box(0), v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; lean_object* v___x_1258_; 
v_val_1257_ = lean_ctor_get(v_fst_1254_, 0);
lean_inc(v_val_1257_);
lean_dec_ref(v_fst_1254_);
v___x_1258_ = lean_apply_2(v_toPure_1252_, lean_box(0), v_val_1257_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1259_, lean_object* v_toPure_1260_, lean_object* v___x_1261_, lean_object* v_____do__lift_1262_){
_start:
{
if (lean_obj_tag(v_____do__lift_1262_) == 1)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v___x_1261_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_____do__lift_1262_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1259_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = lean_apply_2(v_toPure_1260_, lean_box(0), v___x_1265_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec(v_____do__lift_1262_);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1261_);
v___x_1268_ = lean_apply_2(v_toPure_1260_, lean_box(0), v___x_1267_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1269_, lean_object* v_toBind_1270_, lean_object* v___f_1271_, lean_object* v_a_1272_, lean_object* v_x_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_apply_1(v_f_1269_, v_a_1272_);
v___x_1276_ = lean_apply_4(v_toBind_1270_, lean_box(0), lean_box(0), v___x_1275_, v___f_1271_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1277_, lean_object* v_toBind_1278_, lean_object* v___f_1279_, lean_object* v_a_1280_, lean_object* v_x_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1277_, v_toBind_1278_, v___f_1279_, v_a_1280_, v_x_1281_, v___y_1282_);
lean_dec_ref(v___y_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1287_, lean_object* v_f_1288_, lean_object* v_toBind_1289_, lean_object* v___f_1290_, lean_object* v_a_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1287_, v_f_1288_, v_toBind_1289_, v___f_1290_, v_a_1291_, v_x_1292_, v___y_1293_);
lean_dec_ref(v___y_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1295_, lean_object* v_f_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v_toApplicative_1298_; lean_object* v_cs_1299_; lean_object* v_toBind_1300_; lean_object* v_toPure_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___f_1304_; lean_object* v___f_1305_; lean_object* v___f_1306_; size_t v_sz_1307_; size_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_toApplicative_1298_ = lean_ctor_get(v_inst_1295_, 0);
v_cs_1299_ = lean_ctor_get(v_x_1297_, 0);
lean_inc_ref(v_cs_1299_);
lean_dec_ref(v_x_1297_);
v_toBind_1300_ = lean_ctor_get(v_inst_1295_, 1);
lean_inc_n(v_toBind_1300_, 2);
v_toPure_1301_ = lean_ctor_get(v_toApplicative_1298_, 1);
v___x_1302_ = lean_box(0);
v___x_1303_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1301_, 2);
v___f_1304_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1304_, 0, v_toPure_1301_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1305_, 0, v___x_1302_);
lean_closure_set(v___f_1305_, 1, v_toPure_1301_);
lean_closure_set(v___f_1305_, 2, v___x_1303_);
lean_inc_ref(v_inst_1295_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1306_, 0, v_inst_1295_);
lean_closure_set(v___f_1306_, 1, v_f_1296_);
lean_closure_set(v___f_1306_, 2, v_toBind_1300_);
lean_closure_set(v___f_1306_, 3, v___f_1305_);
v_sz_1307_ = lean_array_size(v_cs_1299_);
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1295_, v_cs_1299_, v___f_1306_, v_sz_1307_, v___x_1308_, v___x_1303_);
v___x_1310_ = lean_apply_4(v_toBind_1300_, lean_box(0), lean_box(0), v___x_1309_, v___f_1304_);
return v___x_1310_;
}
else
{
lean_object* v_toApplicative_1311_; lean_object* v_vs_1312_; lean_object* v_toBind_1313_; lean_object* v_toPure_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_toApplicative_1311_ = lean_ctor_get(v_inst_1295_, 0);
v_vs_1312_ = lean_ctor_get(v_x_1297_, 0);
lean_inc_ref(v_vs_1312_);
lean_dec_ref(v_x_1297_);
v_toBind_1313_ = lean_ctor_get(v_inst_1295_, 1);
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
v___f_1319_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1319_, 0, v_f_1296_);
lean_closure_set(v___f_1319_, 1, v_toBind_1313_);
lean_closure_set(v___f_1319_, 2, v___f_1318_);
v_sz_1320_ = lean_array_size(v_vs_1312_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1295_, v_vs_1312_, v___f_1319_, v_sz_1320_, v___x_1321_, v___x_1316_);
v___x_1323_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1322_, v___f_1317_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1324_, lean_object* v_f_1325_, lean_object* v_toBind_1326_, lean_object* v___f_1327_, lean_object* v_a_1328_, lean_object* v_x_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1324_, v_f_1325_, v_a_1328_);
v___x_1332_ = lean_apply_4(v_toBind_1326_, lean_box(0), lean_box(0), v___x_1331_, v___f_1327_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1333_, lean_object* v_m_1334_, lean_object* v_inst_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_f_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1335_, v_f_1337_, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1340_, lean_object* v_____do__lift_1341_, lean_object* v_____s_1342_){
_start:
{
lean_object* v_fst_1343_; 
v_fst_1343_ = lean_ctor_get(v_____s_1342_, 0);
lean_inc(v_fst_1343_);
lean_dec_ref(v_____s_1342_);
if (lean_obj_tag(v_fst_1343_) == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_apply_2(v_toPure_1340_, lean_box(0), v_____do__lift_1341_);
return v___x_1344_;
}
else
{
lean_object* v_val_1345_; lean_object* v___x_1346_; 
lean_dec(v_____do__lift_1341_);
v_val_1345_ = lean_ctor_get(v_fst_1343_, 0);
lean_inc(v_val_1345_);
lean_dec_ref(v_fst_1343_);
v___x_1346_ = lean_apply_2(v_toPure_1340_, lean_box(0), v_val_1345_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1347_, lean_object* v_toPure_1348_, lean_object* v___x_1349_, lean_object* v_____do__lift_1350_){
_start:
{
if (lean_obj_tag(v_____do__lift_1350_) == 1)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_____do__lift_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1347_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
v___x_1354_ = lean_apply_2(v_toPure_1348_, lean_box(0), v___x_1353_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_____do__lift_1350_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1349_);
v___x_1356_ = lean_apply_2(v_toPure_1348_, lean_box(0), v___x_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1357_, lean_object* v_toBind_1358_, lean_object* v___f_1359_, lean_object* v_a_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_apply_1(v_f_1357_, v_a_1360_);
v___x_1364_ = lean_apply_4(v_toBind_1358_, lean_box(0), lean_box(0), v___x_1363_, v___f_1359_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1365_, lean_object* v_toBind_1366_, lean_object* v___f_1367_, lean_object* v_a_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1365_, v_toBind_1366_, v___f_1367_, v_a_1368_, v_x_1369_, v___y_1370_);
lean_dec_ref(v___y_1370_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1372_, lean_object* v_f_1373_, lean_object* v_toBind_1374_, lean_object* v_tail_1375_, lean_object* v_inst_1376_, lean_object* v_____do__lift_1377_){
_start:
{
if (lean_obj_tag(v_____do__lift_1377_) == 0)
{
lean_object* v___f_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; size_t v_sz_1383_; size_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_inc(v_toPure_1372_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1378_, 0, v_toPure_1372_);
lean_closure_set(v___f_1378_, 1, v_____do__lift_1377_);
v___x_1379_ = lean_box(0);
v___x_1380_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1381_, 0, v___x_1379_);
lean_closure_set(v___f_1381_, 1, v_toPure_1372_);
lean_closure_set(v___f_1381_, 2, v___x_1380_);
lean_inc(v_toBind_1374_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1382_, 0, v_f_1373_);
lean_closure_set(v___f_1382_, 1, v_toBind_1374_);
lean_closure_set(v___f_1382_, 2, v___f_1381_);
v_sz_1383_ = lean_array_size(v_tail_1375_);
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1376_, v_tail_1375_, v___f_1382_, v_sz_1383_, v___x_1384_, v___x_1380_);
v___x_1386_ = lean_apply_4(v_toBind_1374_, lean_box(0), lean_box(0), v___x_1385_, v___f_1378_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; 
lean_dec_ref(v_inst_1376_);
lean_dec_ref(v_tail_1375_);
lean_dec(v_toBind_1374_);
lean_dec(v_f_1373_);
v___x_1387_ = lean_apply_2(v_toPure_1372_, lean_box(0), v_____do__lift_1377_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1388_, lean_object* v_t_1389_, lean_object* v_f_1390_){
_start:
{
lean_object* v_toApplicative_1391_; lean_object* v_toBind_1392_; lean_object* v_root_1393_; lean_object* v_tail_1394_; lean_object* v_toPure_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; 
v_toApplicative_1391_ = lean_ctor_get(v_inst_1388_, 0);
v_toBind_1392_ = lean_ctor_get(v_inst_1388_, 1);
lean_inc_n(v_toBind_1392_, 2);
v_root_1393_ = lean_ctor_get(v_t_1389_, 0);
lean_inc_ref(v_root_1393_);
v_tail_1394_ = lean_ctor_get(v_t_1389_, 1);
lean_inc_ref(v_tail_1394_);
lean_dec_ref(v_t_1389_);
v_toPure_1395_ = lean_ctor_get(v_toApplicative_1391_, 1);
lean_inc(v_toPure_1395_);
lean_inc(v_f_1390_);
lean_inc_ref(v_inst_1388_);
v___x_1396_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1388_, v_f_1390_, v_root_1393_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1397_, 0, v_toPure_1395_);
lean_closure_set(v___f_1397_, 1, v_f_1390_);
lean_closure_set(v___f_1397_, 2, v_toBind_1392_);
lean_closure_set(v___f_1397_, 3, v_tail_1394_);
lean_closure_set(v___f_1397_, 4, v_inst_1388_);
v___x_1398_ = lean_apply_4(v_toBind_1392_, lean_box(0), lean_box(0), v___x_1396_, v___f_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1399_, lean_object* v_m_1400_, lean_object* v_inst_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_t_1403_, lean_object* v_f_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1401_, v_t_1403_, v_f_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1406_, lean_object* v_f_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v_cs_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_cs_1409_ = lean_ctor_get(v_x_1408_, 0);
lean_inc_ref(v_cs_1409_);
lean_dec_ref(v_x_1408_);
lean_inc_ref(v_inst_1406_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1410_, 0, v_inst_1406_);
lean_closure_set(v___f_1410_, 1, v_f_1407_);
v___x_1411_ = lean_array_get_size(v_cs_1409_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1406_, v___f_1410_, v_cs_1409_, v___x_1411_, lean_box(0));
return v___x_1412_;
}
else
{
lean_object* v_vs_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_vs_1413_ = lean_ctor_get(v_x_1408_, 0);
lean_inc_ref(v_vs_1413_);
lean_dec_ref(v_x_1408_);
v___x_1414_ = lean_array_get_size(v_vs_1413_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1406_, v_f_1407_, v_vs_1413_, v___x_1414_, lean_box(0));
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1416_, lean_object* v_f_1417_, lean_object* v_c_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1416_, v_f_1417_, v_c_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1420_, lean_object* v_m_1421_, lean_object* v_inst_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_f_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1422_, v_f_1424_, v_x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1427_, lean_object* v_f_1428_, lean_object* v_root_1429_, lean_object* v_toPure_1430_, lean_object* v_____do__lift_1431_){
_start:
{
if (lean_obj_tag(v_____do__lift_1431_) == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_toPure_1430_);
v___x_1432_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1427_, v_f_1428_, v_root_1429_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v_root_1429_);
lean_dec(v_f_1428_);
lean_dec_ref(v_inst_1427_);
v___x_1433_ = lean_apply_2(v_toPure_1430_, lean_box(0), v_____do__lift_1431_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1434_, lean_object* v_t_1435_, lean_object* v_f_1436_){
_start:
{
lean_object* v_toApplicative_1437_; lean_object* v_toBind_1438_; lean_object* v_root_1439_; lean_object* v_tail_1440_; lean_object* v_toPure_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; 
v_toApplicative_1437_ = lean_ctor_get(v_inst_1434_, 0);
v_toBind_1438_ = lean_ctor_get(v_inst_1434_, 1);
lean_inc(v_toBind_1438_);
v_root_1439_ = lean_ctor_get(v_t_1435_, 0);
lean_inc_ref(v_root_1439_);
v_tail_1440_ = lean_ctor_get(v_t_1435_, 1);
lean_inc_ref(v_tail_1440_);
lean_dec_ref(v_t_1435_);
v_toPure_1441_ = lean_ctor_get(v_toApplicative_1437_, 1);
lean_inc(v_toPure_1441_);
v___x_1442_ = lean_array_get_size(v_tail_1440_);
lean_inc(v_f_1436_);
lean_inc_ref(v_inst_1434_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1434_, v_f_1436_, v_tail_1440_, v___x_1442_, lean_box(0));
v___f_1444_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1444_, 0, v_inst_1434_);
lean_closure_set(v___f_1444_, 1, v_f_1436_);
lean_closure_set(v___f_1444_, 2, v_root_1439_);
lean_closure_set(v___f_1444_, 3, v_toPure_1441_);
v___x_1445_ = lean_apply_4(v_toBind_1438_, lean_box(0), lean_box(0), v___x_1443_, v___f_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1446_, lean_object* v_m_1447_, lean_object* v_inst_1448_, lean_object* v_00_u03b2_1449_, lean_object* v_t_1450_, lean_object* v_f_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1448_, v_t_1450_, v_f_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_apply_1(v_f_1453_, v___y_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1457_, lean_object* v_f_1458_, lean_object* v_x_1459_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v_cs_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_cs_1460_ = lean_ctor_get(v_x_1459_, 0);
lean_inc_ref(v_cs_1460_);
lean_dec_ref(v_x_1459_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_get_size(v_cs_1460_);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_nat_dec_lt(v___x_1461_, v___x_1462_);
if (v___x_1464_ == 0)
{
lean_object* v_toApplicative_1465_; lean_object* v_toPure_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_cs_1460_);
lean_dec(v_f_1458_);
v_toApplicative_1465_ = lean_ctor_get(v_inst_1457_, 0);
lean_inc_ref(v_toApplicative_1465_);
lean_dec_ref(v_inst_1457_);
v_toPure_1466_ = lean_ctor_get(v_toApplicative_1465_, 1);
lean_inc(v_toPure_1466_);
lean_dec_ref(v_toApplicative_1465_);
v___x_1467_ = lean_apply_2(v_toPure_1466_, lean_box(0), v___x_1463_);
return v___x_1467_;
}
else
{
lean_object* v___f_1468_; uint8_t v___x_1469_; 
lean_inc_ref(v_inst_1457_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1468_, 0, v_inst_1457_);
lean_closure_set(v___f_1468_, 1, v_f_1458_);
v___x_1469_ = lean_nat_dec_le(v___x_1462_, v___x_1462_);
if (v___x_1469_ == 0)
{
if (v___x_1464_ == 0)
{
lean_object* v_toApplicative_1470_; lean_object* v_toPure_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v___f_1468_);
lean_dec_ref(v_cs_1460_);
v_toApplicative_1470_ = lean_ctor_get(v_inst_1457_, 0);
lean_inc_ref(v_toApplicative_1470_);
lean_dec_ref(v_inst_1457_);
v_toPure_1471_ = lean_ctor_get(v_toApplicative_1470_, 1);
lean_inc(v_toPure_1471_);
lean_dec_ref(v_toApplicative_1470_);
v___x_1472_ = lean_apply_2(v_toPure_1471_, lean_box(0), v___x_1463_);
return v___x_1472_;
}
else
{
size_t v___x_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = ((size_t)0ULL);
v___x_1474_ = lean_usize_of_nat(v___x_1462_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1457_, v___f_1468_, v_cs_1460_, v___x_1473_, v___x_1474_, v___x_1463_);
return v___x_1475_;
}
}
else
{
size_t v___x_1476_; size_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = ((size_t)0ULL);
v___x_1477_ = lean_usize_of_nat(v___x_1462_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1457_, v___f_1468_, v_cs_1460_, v___x_1476_, v___x_1477_, v___x_1463_);
return v___x_1478_;
}
}
}
else
{
lean_object* v_vs_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v_vs_1479_ = lean_ctor_get(v_x_1459_, 0);
lean_inc_ref(v_vs_1479_);
lean_dec_ref(v_x_1459_);
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_array_get_size(v_vs_1479_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_nat_dec_lt(v___x_1480_, v___x_1481_);
if (v___x_1483_ == 0)
{
lean_object* v_toApplicative_1484_; lean_object* v_toPure_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_vs_1479_);
lean_dec(v_f_1458_);
v_toApplicative_1484_ = lean_ctor_get(v_inst_1457_, 0);
lean_inc_ref(v_toApplicative_1484_);
lean_dec_ref(v_inst_1457_);
v_toPure_1485_ = lean_ctor_get(v_toApplicative_1484_, 1);
lean_inc(v_toPure_1485_);
lean_dec_ref(v_toApplicative_1484_);
v___x_1486_ = lean_apply_2(v_toPure_1485_, lean_box(0), v___x_1482_);
return v___x_1486_;
}
else
{
lean_object* v___f_1487_; uint8_t v___x_1488_; 
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1487_, 0, v_f_1458_);
v___x_1488_ = lean_nat_dec_le(v___x_1481_, v___x_1481_);
if (v___x_1488_ == 0)
{
if (v___x_1483_ == 0)
{
lean_object* v_toApplicative_1489_; lean_object* v_toPure_1490_; lean_object* v___x_1491_; 
lean_dec_ref(v___f_1487_);
lean_dec_ref(v_vs_1479_);
v_toApplicative_1489_ = lean_ctor_get(v_inst_1457_, 0);
lean_inc_ref(v_toApplicative_1489_);
lean_dec_ref(v_inst_1457_);
v_toPure_1490_ = lean_ctor_get(v_toApplicative_1489_, 1);
lean_inc(v_toPure_1490_);
lean_dec_ref(v_toApplicative_1489_);
v___x_1491_ = lean_apply_2(v_toPure_1490_, lean_box(0), v___x_1482_);
return v___x_1491_;
}
else
{
size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = lean_usize_of_nat(v___x_1481_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1457_, v___f_1487_, v_vs_1479_, v___x_1492_, v___x_1493_, v___x_1482_);
return v___x_1494_;
}
}
else
{
size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_of_nat(v___x_1481_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1457_, v___f_1487_, v_vs_1479_, v___x_1495_, v___x_1496_, v___x_1482_);
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1498_, lean_object* v_f_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1498_, v_f_1499_, v___y_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1503_, lean_object* v_m_1504_, lean_object* v_inst_1505_, lean_object* v_f_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1505_, v_f_1506_, v_x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_apply_1(v_f_1509_, v___y_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1513_, lean_object* v_toPure_1514_, lean_object* v_inst_1515_, lean_object* v___f_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_array_get_size(v_tail_1513_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_nat_dec_lt(v___x_1518_, v___x_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec(v___f_1516_);
lean_dec_ref(v_inst_1515_);
lean_dec_ref(v_tail_1513_);
v___x_1522_ = lean_apply_2(v_toPure_1514_, lean_box(0), v___x_1520_);
return v___x_1522_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_nat_dec_le(v___x_1519_, v___x_1519_);
if (v___x_1523_ == 0)
{
if (v___x_1521_ == 0)
{
lean_object* v___x_1524_; 
lean_dec(v___f_1516_);
lean_dec_ref(v_inst_1515_);
lean_dec_ref(v_tail_1513_);
v___x_1524_ = lean_apply_2(v_toPure_1514_, lean_box(0), v___x_1520_);
return v___x_1524_;
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_toPure_1514_);
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1519_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1515_, v___f_1516_, v_tail_1513_, v___x_1525_, v___x_1526_, v___x_1520_);
return v___x_1527_;
}
}
else
{
size_t v___x_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_toPure_1514_);
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = lean_usize_of_nat(v___x_1519_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1515_, v___f_1516_, v_tail_1513_, v___x_1528_, v___x_1529_, v___x_1520_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1531_, lean_object* v_t_1532_, lean_object* v_f_1533_){
_start:
{
lean_object* v_toApplicative_1534_; lean_object* v_toPure_1535_; lean_object* v_toSeqRight_1536_; lean_object* v_root_1537_; lean_object* v_tail_1538_; lean_object* v___f_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_toApplicative_1534_ = lean_ctor_get(v_inst_1531_, 0);
v_toPure_1535_ = lean_ctor_get(v_toApplicative_1534_, 1);
v_toSeqRight_1536_ = lean_ctor_get(v_toApplicative_1534_, 4);
lean_inc(v_toSeqRight_1536_);
v_root_1537_ = lean_ctor_get(v_t_1532_, 0);
lean_inc_ref(v_root_1537_);
v_tail_1538_ = lean_ctor_get(v_t_1532_, 1);
lean_inc_ref(v_tail_1538_);
lean_dec_ref(v_t_1532_);
lean_inc(v_f_1533_);
v___f_1539_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1539_, 0, v_f_1533_);
lean_inc_ref(v_inst_1531_);
lean_inc(v_toPure_1535_);
v___f_1540_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1540_, 0, v_tail_1538_);
lean_closure_set(v___f_1540_, 1, v_toPure_1535_);
lean_closure_set(v___f_1540_, 2, v_inst_1531_);
lean_closure_set(v___f_1540_, 3, v___f_1539_);
v___x_1541_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1531_, v_f_1533_, v_root_1537_);
v___x_1542_ = lean_apply_4(v_toSeqRight_1536_, lean_box(0), lean_box(0), v___x_1541_, v___f_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1543_, lean_object* v_m_1544_, lean_object* v_inst_1545_, lean_object* v_t_1546_, lean_object* v_f_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1545_, v_t_1546_, v_f_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_j_1549_, lean_object* v_cs_1550_, lean_object* v_toApplicative_1551_, lean_object* v_inst_1552_, lean_object* v___f_1553_, lean_object* v_____r_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_j_1549_, v___x_1555_);
v___x_1557_ = lean_array_get_size(v_cs_1550_);
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1559_ == 0)
{
lean_object* v_toPure_1560_; lean_object* v___x_1561_; 
lean_dec(v___x_1556_);
lean_dec(v___f_1553_);
lean_dec_ref(v_inst_1552_);
lean_dec_ref(v_cs_1550_);
v_toPure_1560_ = lean_ctor_get(v_toApplicative_1551_, 1);
lean_inc(v_toPure_1560_);
lean_dec_ref(v_toApplicative_1551_);
v___x_1561_ = lean_apply_2(v_toPure_1560_, lean_box(0), v___x_1558_);
return v___x_1561_;
}
else
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_nat_dec_le(v___x_1557_, v___x_1557_);
if (v___x_1562_ == 0)
{
if (v___x_1559_ == 0)
{
lean_object* v_toPure_1563_; lean_object* v___x_1564_; 
lean_dec(v___x_1556_);
lean_dec(v___f_1553_);
lean_dec_ref(v_inst_1552_);
lean_dec_ref(v_cs_1550_);
v_toPure_1563_ = lean_ctor_get(v_toApplicative_1551_, 1);
lean_inc(v_toPure_1563_);
lean_dec_ref(v_toApplicative_1551_);
v___x_1564_ = lean_apply_2(v_toPure_1563_, lean_box(0), v___x_1558_);
return v___x_1564_;
}
else
{
size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v_toApplicative_1551_);
v___x_1565_ = lean_usize_of_nat(v___x_1556_);
lean_dec(v___x_1556_);
v___x_1566_ = lean_usize_of_nat(v___x_1557_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1552_, v___f_1553_, v_cs_1550_, v___x_1565_, v___x_1566_, v___x_1558_);
return v___x_1567_;
}
}
else
{
size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_toApplicative_1551_);
v___x_1568_ = lean_usize_of_nat(v___x_1556_);
lean_dec(v___x_1556_);
v___x_1569_ = lean_usize_of_nat(v___x_1557_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1552_, v___f_1553_, v_cs_1550_, v___x_1568_, v___x_1569_, v___x_1558_);
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_j_1571_, lean_object* v_cs_1572_, lean_object* v_toApplicative_1573_, lean_object* v_inst_1574_, lean_object* v___f_1575_, lean_object* v_____r_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_j_1571_, v_cs_1572_, v_toApplicative_1573_, v_inst_1574_, v___f_1575_, v_____r_1576_);
lean_dec(v_j_1571_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1578_, lean_object* v_f_1579_, lean_object* v_x_1580_, size_t v_x_1581_, size_t v_x_1582_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
lean_object* v_toApplicative_1583_; lean_object* v_toBind_1584_; lean_object* v_cs_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; size_t v___x_1588_; lean_object* v_j_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_toApplicative_1583_ = lean_ctor_get(v_inst_1578_, 0);
v_toBind_1584_ = lean_ctor_get(v_inst_1578_, 1);
lean_inc(v_toBind_1584_);
v_cs_1585_ = lean_ctor_get(v_x_1580_, 0);
lean_inc_ref_n(v_cs_1585_, 2);
lean_dec_ref(v_x_1580_);
lean_inc(v_f_1579_);
lean_inc_ref_n(v_inst_1578_, 2);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1586_, 0, v_inst_1578_);
lean_closure_set(v___f_1586_, 1, v_f_1579_);
v___x_1587_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1588_ = lean_usize_shift_right(v_x_1581_, v_x_1582_);
v_j_1589_ = lean_usize_to_nat(v___x_1588_);
lean_inc_ref(v_toApplicative_1583_);
lean_inc(v_j_1589_);
v___f_1590_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1590_, 0, v_j_1589_);
lean_closure_set(v___f_1590_, 1, v_cs_1585_);
lean_closure_set(v___f_1590_, 2, v_toApplicative_1583_);
lean_closure_set(v___f_1590_, 3, v_inst_1578_);
lean_closure_set(v___f_1590_, 4, v___f_1586_);
v___x_1591_ = lean_array_get(v___x_1587_, v_cs_1585_, v_j_1589_);
lean_dec(v_j_1589_);
lean_dec_ref(v_cs_1585_);
v___x_1592_ = ((size_t)1ULL);
v___x_1593_ = lean_usize_shift_left(v___x_1592_, v_x_1582_);
v___x_1594_ = lean_usize_sub(v___x_1593_, v___x_1592_);
v___x_1595_ = lean_usize_land(v_x_1581_, v___x_1594_);
v___x_1596_ = ((size_t)5ULL);
v___x_1597_ = lean_usize_sub(v_x_1582_, v___x_1596_);
v___x_1598_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1578_, v_f_1579_, v___x_1591_, v___x_1595_, v___x_1597_);
v___x_1599_ = lean_apply_4(v_toBind_1584_, lean_box(0), lean_box(0), v___x_1598_, v___f_1590_);
return v___x_1599_;
}
else
{
lean_object* v_toApplicative_1600_; lean_object* v_vs_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_toApplicative_1600_ = lean_ctor_get(v_inst_1578_, 0);
v_vs_1601_ = lean_ctor_get(v_x_1580_, 0);
lean_inc_ref(v_vs_1601_);
lean_dec_ref(v_x_1580_);
v___x_1602_ = lean_usize_to_nat(v_x_1581_);
v___x_1603_ = lean_array_get_size(v_vs_1601_);
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_nat_dec_lt(v___x_1602_, v___x_1603_);
if (v___x_1605_ == 0)
{
lean_object* v_toPure_1606_; lean_object* v___x_1607_; 
lean_inc_ref(v_toApplicative_1600_);
lean_dec(v___x_1602_);
lean_dec_ref(v_vs_1601_);
lean_dec(v_f_1579_);
lean_dec_ref(v_inst_1578_);
v_toPure_1606_ = lean_ctor_get(v_toApplicative_1600_, 1);
lean_inc(v_toPure_1606_);
lean_dec_ref(v_toApplicative_1600_);
v___x_1607_ = lean_apply_2(v_toPure_1606_, lean_box(0), v___x_1604_);
return v___x_1607_;
}
else
{
lean_object* v___f_1608_; uint8_t v___x_1609_; 
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1608_, 0, v_f_1579_);
v___x_1609_ = lean_nat_dec_le(v___x_1603_, v___x_1603_);
if (v___x_1609_ == 0)
{
if (v___x_1605_ == 0)
{
lean_object* v_toPure_1610_; lean_object* v___x_1611_; 
lean_inc_ref(v_toApplicative_1600_);
lean_dec_ref(v___f_1608_);
lean_dec(v___x_1602_);
lean_dec_ref(v_vs_1601_);
lean_dec_ref(v_inst_1578_);
v_toPure_1610_ = lean_ctor_get(v_toApplicative_1600_, 1);
lean_inc(v_toPure_1610_);
lean_dec_ref(v_toApplicative_1600_);
v___x_1611_ = lean_apply_2(v_toPure_1610_, lean_box(0), v___x_1604_);
return v___x_1611_;
}
else
{
size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_usize_of_nat(v___x_1602_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_usize_of_nat(v___x_1603_);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1578_, v___f_1608_, v_vs_1601_, v___x_1612_, v___x_1613_, v___x_1604_);
return v___x_1614_;
}
}
else
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_usize_of_nat(v___x_1602_);
lean_dec(v___x_1602_);
v___x_1616_ = lean_usize_of_nat(v___x_1603_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1578_, v___f_1608_, v_vs_1601_, v___x_1615_, v___x_1616_, v___x_1604_);
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1618_, lean_object* v_f_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
size_t v_x_290__boxed_1623_; size_t v_x_291__boxed_1624_; lean_object* v_res_1625_; 
v_x_290__boxed_1623_ = lean_unbox_usize(v_x_1621_);
lean_dec(v_x_1621_);
v_x_291__boxed_1624_ = lean_unbox_usize(v_x_1622_);
lean_dec(v_x_1622_);
v_res_1625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1618_, v_f_1619_, v_x_1620_, v_x_290__boxed_1623_, v_x_291__boxed_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1626_, lean_object* v_m_1627_, lean_object* v_inst_1628_, lean_object* v_f_1629_, lean_object* v_x_1630_, size_t v_x_1631_, size_t v_x_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1628_, v_f_1629_, v_x_1630_, v_x_1631_, v_x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_m_1635_, lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
size_t v_x_360__boxed_1641_; size_t v_x_361__boxed_1642_; lean_object* v_res_1643_; 
v_x_360__boxed_1641_ = lean_unbox_usize(v_x_1639_);
lean_dec(v_x_1639_);
v_x_361__boxed_1642_ = lean_unbox_usize(v_x_1640_);
lean_dec(v_x_1640_);
v_res_1643_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1634_, v_m_1635_, v_inst_1636_, v_f_1637_, v_x_1638_, v_x_360__boxed_1641_, v_x_361__boxed_1642_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_tail_1644_, lean_object* v___x_1645_, lean_object* v_toApplicative_1646_, lean_object* v_inst_1647_, lean_object* v___f_1648_, lean_object* v_____r_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1650_ = lean_array_get_size(v_tail_1644_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_nat_dec_lt(v___x_1645_, v___x_1650_);
if (v___x_1652_ == 0)
{
lean_object* v_toPure_1653_; lean_object* v___x_1654_; 
lean_dec(v___f_1648_);
lean_dec_ref(v_inst_1647_);
lean_dec_ref(v_tail_1644_);
v_toPure_1653_ = lean_ctor_get(v_toApplicative_1646_, 1);
lean_inc(v_toPure_1653_);
lean_dec_ref(v_toApplicative_1646_);
v___x_1654_ = lean_apply_2(v_toPure_1653_, lean_box(0), v___x_1651_);
return v___x_1654_;
}
else
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_nat_dec_le(v___x_1650_, v___x_1650_);
if (v___x_1655_ == 0)
{
if (v___x_1652_ == 0)
{
lean_object* v_toPure_1656_; lean_object* v___x_1657_; 
lean_dec(v___f_1648_);
lean_dec_ref(v_inst_1647_);
lean_dec_ref(v_tail_1644_);
v_toPure_1656_ = lean_ctor_get(v_toApplicative_1646_, 1);
lean_inc(v_toPure_1656_);
lean_dec_ref(v_toApplicative_1646_);
v___x_1657_ = lean_apply_2(v_toPure_1656_, lean_box(0), v___x_1651_);
return v___x_1657_;
}
else
{
size_t v___x_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
lean_dec_ref(v_toApplicative_1646_);
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = lean_usize_of_nat(v___x_1650_);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1647_, v___f_1648_, v_tail_1644_, v___x_1658_, v___x_1659_, v___x_1651_);
return v___x_1660_;
}
}
else
{
size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v_toApplicative_1646_);
v___x_1661_ = ((size_t)0ULL);
v___x_1662_ = lean_usize_of_nat(v___x_1650_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1647_, v___f_1648_, v_tail_1644_, v___x_1661_, v___x_1662_, v___x_1651_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_tail_1664_, lean_object* v___x_1665_, lean_object* v_toApplicative_1666_, lean_object* v_inst_1667_, lean_object* v___f_1668_, lean_object* v_____r_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_tail_1664_, v___x_1665_, v_toApplicative_1666_, v_inst_1667_, v___f_1668_, v_____r_1669_);
lean_dec(v___x_1665_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1671_, lean_object* v_t_1672_, lean_object* v_f_1673_, lean_object* v_start_1674_){
_start:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_nat_dec_eq(v_start_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v_root_1677_; lean_object* v_tail_1678_; size_t v_shift_1679_; lean_object* v_tailOff_1680_; uint8_t v___x_1681_; 
v_root_1677_ = lean_ctor_get(v_t_1672_, 0);
lean_inc_ref(v_root_1677_);
v_tail_1678_ = lean_ctor_get(v_t_1672_, 1);
lean_inc_ref(v_tail_1678_);
v_shift_1679_ = lean_ctor_get_usize(v_t_1672_, 4);
v_tailOff_1680_ = lean_ctor_get(v_t_1672_, 3);
lean_inc(v_tailOff_1680_);
lean_dec_ref(v_t_1672_);
v___x_1681_ = lean_nat_dec_le(v_tailOff_1680_, v_start_1674_);
if (v___x_1681_ == 0)
{
lean_object* v_toApplicative_1682_; lean_object* v_toBind_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; size_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_tailOff_1680_);
v_toApplicative_1682_ = lean_ctor_get(v_inst_1671_, 0);
v_toBind_1683_ = lean_ctor_get(v_inst_1671_, 1);
lean_inc(v_toBind_1683_);
lean_inc(v_f_1673_);
v___f_1684_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1684_, 0, v_f_1673_);
lean_inc_ref(v_inst_1671_);
lean_inc_ref(v_toApplicative_1682_);
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1685_, 0, v_tail_1678_);
lean_closure_set(v___f_1685_, 1, v___x_1675_);
lean_closure_set(v___f_1685_, 2, v_toApplicative_1682_);
lean_closure_set(v___f_1685_, 3, v_inst_1671_);
lean_closure_set(v___f_1685_, 4, v___f_1684_);
v___x_1686_ = lean_usize_of_nat(v_start_1674_);
v___x_1687_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1671_, v_f_1673_, v_root_1677_, v___x_1686_, v_shift_1679_);
v___x_1688_ = lean_apply_4(v_toBind_1683_, lean_box(0), lean_box(0), v___x_1687_, v___f_1685_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
lean_dec_ref(v_root_1677_);
v___x_1689_ = lean_nat_sub(v_start_1674_, v_tailOff_1680_);
lean_dec(v_tailOff_1680_);
v___x_1690_ = lean_array_get_size(v_tail_1678_);
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_nat_dec_lt(v___x_1689_, v___x_1690_);
if (v___x_1692_ == 0)
{
lean_object* v_toApplicative_1693_; lean_object* v_toPure_1694_; lean_object* v___x_1695_; 
lean_dec(v___x_1689_);
lean_dec_ref(v_tail_1678_);
lean_dec(v_f_1673_);
v_toApplicative_1693_ = lean_ctor_get(v_inst_1671_, 0);
lean_inc_ref(v_toApplicative_1693_);
lean_dec_ref(v_inst_1671_);
v_toPure_1694_ = lean_ctor_get(v_toApplicative_1693_, 1);
lean_inc(v_toPure_1694_);
lean_dec_ref(v_toApplicative_1693_);
v___x_1695_ = lean_apply_2(v_toPure_1694_, lean_box(0), v___x_1691_);
return v___x_1695_;
}
else
{
lean_object* v___f_1696_; uint8_t v___x_1697_; 
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1696_, 0, v_f_1673_);
v___x_1697_ = lean_nat_dec_le(v___x_1690_, v___x_1690_);
if (v___x_1697_ == 0)
{
if (v___x_1692_ == 0)
{
lean_object* v_toApplicative_1698_; lean_object* v_toPure_1699_; lean_object* v___x_1700_; 
lean_dec_ref(v___f_1696_);
lean_dec(v___x_1689_);
lean_dec_ref(v_tail_1678_);
v_toApplicative_1698_ = lean_ctor_get(v_inst_1671_, 0);
lean_inc_ref(v_toApplicative_1698_);
lean_dec_ref(v_inst_1671_);
v_toPure_1699_ = lean_ctor_get(v_toApplicative_1698_, 1);
lean_inc(v_toPure_1699_);
lean_dec_ref(v_toApplicative_1698_);
v___x_1700_ = lean_apply_2(v_toPure_1699_, lean_box(0), v___x_1691_);
return v___x_1700_;
}
else
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_usize_of_nat(v___x_1689_);
lean_dec(v___x_1689_);
v___x_1702_ = lean_usize_of_nat(v___x_1690_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1671_, v___f_1696_, v_tail_1678_, v___x_1701_, v___x_1702_, v___x_1691_);
return v___x_1703_;
}
}
else
{
size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_usize_of_nat(v___x_1689_);
lean_dec(v___x_1689_);
v___x_1705_ = lean_usize_of_nat(v___x_1690_);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1671_, v___f_1696_, v_tail_1678_, v___x_1704_, v___x_1705_, v___x_1691_);
return v___x_1706_;
}
}
}
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1671_, v_t_1672_, v_f_1673_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1708_, lean_object* v_t_1709_, lean_object* v_f_1710_, lean_object* v_start_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_PersistentArray_forM___redArg(v_inst_1708_, v_t_1709_, v_f_1710_, v_start_1711_);
lean_dec(v_start_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1713_, lean_object* v_m_1714_, lean_object* v_inst_1715_, lean_object* v_t_1716_, lean_object* v_f_1717_, lean_object* v_start_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentArray_forM___redArg(v_inst_1715_, v_t_1716_, v_f_1717_, v_start_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_m_1721_, lean_object* v_inst_1722_, lean_object* v_t_1723_, lean_object* v_f_1724_, lean_object* v_start_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentArray_forM(v_00_u03b1_1720_, v_m_1721_, v_inst_1722_, v_t_1723_, v_f_1724_, v_start_1725_);
lean_dec(v_start_1725_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1727_, lean_object* v_x1_1728_, lean_object* v_x2_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_apply_2(v_f_1727_, v_x1_1728_, v_x2_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1750_, lean_object* v_f_1751_, lean_object* v_init_1752_, lean_object* v_start_1753_){
_start:
{
lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1754_, 0, v_f_1751_);
v___x_1755_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1756_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1755_, v_t_1750_, v___f_1754_, v_init_1752_, v_start_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1757_, lean_object* v_f_1758_, lean_object* v_init_1759_, lean_object* v_start_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_PersistentArray_foldl___redArg(v_t_1757_, v_f_1758_, v_init_1759_, v_start_1760_);
lean_dec(v_start_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_t_1764_, lean_object* v_f_1765_, lean_object* v_init_1766_, lean_object* v_start_1767_){
_start:
{
lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1768_, 0, v_f_1765_);
v___x_1769_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1770_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1769_, v_t_1764_, v___f_1768_, v_init_1766_, v_start_1767_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1771_, lean_object* v_00_u03b2_1772_, lean_object* v_t_1773_, lean_object* v_f_1774_, lean_object* v_init_1775_, lean_object* v_start_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1771_, v_00_u03b2_1772_, v_t_1773_, v_f_1774_, v_init_1775_, v_start_1776_);
lean_dec(v_start_1776_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1778_, lean_object* v_f_1779_, lean_object* v_init_1780_){
_start:
{
lean_object* v___f_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1781_, 0, v_f_1779_);
v___x_1782_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1783_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1782_, v_t_1778_, v___f_1781_, v_init_1780_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1784_, lean_object* v_00_u03b2_1785_, lean_object* v_t_1786_, lean_object* v_f_1787_, lean_object* v_init_1788_){
_start:
{
lean_object* v___f_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___f_1789_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1789_, 0, v_f_1787_);
v___x_1790_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1791_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1790_, v_t_1786_, v___f_1789_, v_init_1788_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1792_, lean_object* v_x1_1793_, lean_object* v_x2_1794_){
_start:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
lean_inc(v_x2_1794_);
v___x_1795_ = lean_apply_1(v_p_1792_, v_x2_1794_);
v___x_1796_ = lean_unbox(v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec(v_x2_1794_);
return v_x1_1793_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_PersistentArray_push___redArg(v_x1_1793_, v_x2_1794_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1798_, lean_object* v_p_1799_){
_start:
{
lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___f_1800_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1800_, 0, v_p_1799_);
v___x_1801_ = lean_unsigned_to_nat(32u);
v___x_1802_ = lean_mk_empty_array_with_capacity(v___x_1801_);
lean_dec_ref(v___x_1802_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_1805_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1806_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1805_, v_as_1798_, v___f_1800_, v___x_1804_, v___x_1803_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1807_, lean_object* v_as_1808_, lean_object* v_p_1809_){
_start:
{
lean_object* v___f_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1810_, 0, v_p_1809_);
v___x_1811_ = lean_unsigned_to_nat(32u);
v___x_1812_ = lean_mk_empty_array_with_capacity(v___x_1811_);
lean_dec_ref(v___x_1812_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_1815_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1816_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1815_, v_as_1808_, v___f_1810_, v___x_1814_, v___x_1813_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1817_, size_t v_i_1818_, size_t v_stop_1819_, lean_object* v_b_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_eq(v_i_1818_, v_stop_1819_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; size_t v___x_1824_; size_t v___x_1825_; 
v___x_1822_ = lean_array_uget_borrowed(v_as_1817_, v_i_1818_);
lean_inc(v___x_1822_);
v___x_1823_ = lean_array_push(v_b_1820_, v___x_1822_);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_add(v_i_1818_, v___x_1824_);
v_i_1818_ = v___x_1825_;
v_b_1820_ = v___x_1823_;
goto _start;
}
else
{
return v_b_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1827_, lean_object* v_i_1828_, lean_object* v_stop_1829_, lean_object* v_b_1830_){
_start:
{
size_t v_i_boxed_1831_; size_t v_stop_boxed_1832_; lean_object* v_res_1833_; 
v_i_boxed_1831_ = lean_unbox_usize(v_i_1828_);
lean_dec(v_i_1828_);
v_stop_boxed_1832_ = lean_unbox_usize(v_stop_1829_);
lean_dec(v_stop_1829_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1827_, v_i_boxed_1831_, v_stop_boxed_1832_, v_b_1830_);
lean_dec_ref(v_as_1827_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
if (lean_obj_tag(v_x_1834_) == 0)
{
lean_object* v_cs_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_cs_1836_ = lean_ctor_get(v_x_1834_, 0);
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_array_get_size(v_cs_1836_);
v___x_1839_ = lean_nat_dec_lt(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
return v_x_1835_;
}
else
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_nat_dec_le(v___x_1838_, v___x_1838_);
if (v___x_1840_ == 0)
{
if (v___x_1839_ == 0)
{
return v_x_1835_;
}
else
{
size_t v___x_1841_; size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((size_t)0ULL);
v___x_1842_ = lean_usize_of_nat(v___x_1838_);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1836_, v___x_1841_, v___x_1842_, v_x_1835_);
return v___x_1843_;
}
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1838_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1836_, v___x_1844_, v___x_1845_, v_x_1835_);
return v___x_1846_;
}
}
}
else
{
lean_object* v_vs_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_vs_1847_ = lean_ctor_get(v_x_1834_, 0);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_array_get_size(v_vs_1847_);
v___x_1850_ = lean_nat_dec_lt(v___x_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
return v_x_1835_;
}
else
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_nat_dec_le(v___x_1849_, v___x_1849_);
if (v___x_1851_ == 0)
{
if (v___x_1850_ == 0)
{
return v_x_1835_;
}
else
{
size_t v___x_1852_; size_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = lean_usize_of_nat(v___x_1849_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1847_, v___x_1852_, v___x_1853_, v_x_1835_);
return v___x_1854_;
}
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1849_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1847_, v___x_1855_, v___x_1856_, v_x_1835_);
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1858_, size_t v_i_1859_, size_t v_stop_1860_, lean_object* v_b_1861_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_usize_dec_eq(v_i_1859_, v_stop_1860_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; 
v___x_1863_ = lean_array_uget_borrowed(v_as_1858_, v_i_1859_);
v___x_1864_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1863_, v_b_1861_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1859_, v___x_1865_);
v_i_1859_ = v___x_1866_;
v_b_1861_ = v___x_1864_;
goto _start;
}
else
{
return v_b_1861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1868_, lean_object* v_i_1869_, lean_object* v_stop_1870_, lean_object* v_b_1871_){
_start:
{
size_t v_i_boxed_1872_; size_t v_stop_boxed_1873_; lean_object* v_res_1874_; 
v_i_boxed_1872_ = lean_unbox_usize(v_i_1869_);
lean_dec(v_i_1869_);
v_stop_boxed_1873_ = lean_unbox_usize(v_stop_1870_);
lean_dec(v_stop_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1868_, v_i_boxed_1872_, v_stop_boxed_1873_, v_b_1871_);
lean_dec_ref(v_as_1868_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1875_, v_x_1876_);
lean_dec_ref(v_x_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1878_, size_t v_x_1879_, size_t v_x_1880_, lean_object* v_x_1881_){
_start:
{
if (lean_obj_tag(v_x_1878_) == 0)
{
lean_object* v_cs_1882_; lean_object* v___x_1883_; size_t v___x_1884_; lean_object* v_j_1885_; lean_object* v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_cs_1882_ = lean_ctor_get(v_x_1878_, 0);
v___x_1883_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1884_ = lean_usize_shift_right(v_x_1879_, v_x_1880_);
v_j_1885_ = lean_usize_to_nat(v___x_1884_);
v___x_1886_ = lean_array_get_borrowed(v___x_1883_, v_cs_1882_, v_j_1885_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_shift_left(v___x_1887_, v_x_1880_);
v___x_1889_ = lean_usize_sub(v___x_1888_, v___x_1887_);
v___x_1890_ = lean_usize_land(v_x_1879_, v___x_1889_);
v___x_1891_ = ((size_t)5ULL);
v___x_1892_ = lean_usize_sub(v_x_1880_, v___x_1891_);
v___x_1893_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1886_, v___x_1890_, v___x_1892_, v_x_1881_);
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = lean_nat_add(v_j_1885_, v___x_1894_);
lean_dec(v_j_1885_);
v___x_1896_ = lean_array_get_size(v_cs_1882_);
v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v___x_1895_);
return v___x_1893_;
}
else
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_le(v___x_1896_, v___x_1896_);
if (v___x_1898_ == 0)
{
if (v___x_1897_ == 0)
{
lean_dec(v___x_1895_);
return v___x_1893_;
}
else
{
size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_usize_of_nat(v___x_1895_);
lean_dec(v___x_1895_);
v___x_1900_ = lean_usize_of_nat(v___x_1896_);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1882_, v___x_1899_, v___x_1900_, v___x_1893_);
return v___x_1901_;
}
}
else
{
size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_usize_of_nat(v___x_1895_);
lean_dec(v___x_1895_);
v___x_1903_ = lean_usize_of_nat(v___x_1896_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1882_, v___x_1902_, v___x_1903_, v___x_1893_);
return v___x_1904_;
}
}
}
else
{
lean_object* v_vs_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_vs_1905_ = lean_ctor_get(v_x_1878_, 0);
v___x_1906_ = lean_usize_to_nat(v_x_1879_);
v___x_1907_ = lean_array_get_size(v_vs_1905_);
v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_dec(v___x_1906_);
return v_x_1881_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_le(v___x_1907_, v___x_1907_);
if (v___x_1909_ == 0)
{
if (v___x_1908_ == 0)
{
lean_dec(v___x_1906_);
return v_x_1881_;
}
else
{
size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_usize_of_nat(v___x_1906_);
lean_dec(v___x_1906_);
v___x_1911_ = lean_usize_of_nat(v___x_1907_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1905_, v___x_1910_, v___x_1911_, v_x_1881_);
return v___x_1912_;
}
}
else
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_usize_of_nat(v___x_1906_);
lean_dec(v___x_1906_);
v___x_1914_ = lean_usize_of_nat(v___x_1907_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1905_, v___x_1913_, v___x_1914_, v_x_1881_);
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_){
_start:
{
size_t v_x_1497__boxed_1920_; size_t v_x_1498__boxed_1921_; lean_object* v_res_1922_; 
v_x_1497__boxed_1920_ = lean_unbox_usize(v_x_1917_);
lean_dec(v_x_1917_);
v_x_1498__boxed_1921_ = lean_unbox_usize(v_x_1918_);
lean_dec(v_x_1918_);
v_res_1922_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1916_, v_x_1497__boxed_1920_, v_x_1498__boxed_1921_, v_x_1919_);
lean_dec_ref(v_x_1916_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1923_, lean_object* v_init_1924_, lean_object* v_start_1925_){
_start:
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_nat_dec_eq(v_start_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v_root_1928_; lean_object* v_tail_1929_; size_t v_shift_1930_; lean_object* v_tailOff_1931_; uint8_t v___x_1932_; 
v_root_1928_ = lean_ctor_get(v_t_1923_, 0);
v_tail_1929_ = lean_ctor_get(v_t_1923_, 1);
v_shift_1930_ = lean_ctor_get_usize(v_t_1923_, 4);
v_tailOff_1931_ = lean_ctor_get(v_t_1923_, 3);
v___x_1932_ = lean_nat_dec_le(v_tailOff_1931_, v_start_1925_);
if (v___x_1932_ == 0)
{
size_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1933_ = lean_usize_of_nat(v_start_1925_);
v___x_1934_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1928_, v___x_1933_, v_shift_1930_, v_init_1924_);
v___x_1935_ = lean_array_get_size(v_tail_1929_);
v___x_1936_ = lean_nat_dec_lt(v___x_1926_, v___x_1935_);
if (v___x_1936_ == 0)
{
return v___x_1934_;
}
else
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_nat_dec_le(v___x_1935_, v___x_1935_);
if (v___x_1937_ == 0)
{
if (v___x_1936_ == 0)
{
return v___x_1934_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1935_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1929_, v___x_1938_, v___x_1939_, v___x_1934_);
return v___x_1940_;
}
}
else
{
size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1935_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1929_, v___x_1941_, v___x_1942_, v___x_1934_);
return v___x_1943_;
}
}
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = lean_nat_sub(v_start_1925_, v_tailOff_1931_);
v___x_1945_ = lean_array_get_size(v_tail_1929_);
v___x_1946_ = lean_nat_dec_lt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_dec(v___x_1944_);
return v_init_1924_;
}
else
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_nat_dec_le(v___x_1945_, v___x_1945_);
if (v___x_1947_ == 0)
{
if (v___x_1946_ == 0)
{
lean_dec(v___x_1944_);
return v_init_1924_;
}
else
{
size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_usize_of_nat(v___x_1944_);
lean_dec(v___x_1944_);
v___x_1949_ = lean_usize_of_nat(v___x_1945_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1929_, v___x_1948_, v___x_1949_, v_init_1924_);
return v___x_1950_;
}
}
else
{
size_t v___x_1951_; size_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_usize_of_nat(v___x_1944_);
lean_dec(v___x_1944_);
v___x_1952_ = lean_usize_of_nat(v___x_1945_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1929_, v___x_1951_, v___x_1952_, v_init_1924_);
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_root_1954_; lean_object* v_tail_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_root_1954_ = lean_ctor_get(v_t_1923_, 0);
v_tail_1955_ = lean_ctor_get(v_t_1923_, 1);
v___x_1956_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1954_, v_init_1924_);
v___x_1957_ = lean_array_get_size(v_tail_1955_);
v___x_1958_ = lean_nat_dec_lt(v___x_1926_, v___x_1957_);
if (v___x_1958_ == 0)
{
return v___x_1956_;
}
else
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_nat_dec_le(v___x_1957_, v___x_1957_);
if (v___x_1959_ == 0)
{
if (v___x_1958_ == 0)
{
return v___x_1956_;
}
else
{
size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = lean_usize_of_nat(v___x_1957_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1955_, v___x_1960_, v___x_1961_, v___x_1956_);
return v___x_1962_;
}
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1957_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1955_, v___x_1963_, v___x_1964_, v___x_1956_);
return v___x_1965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1966_, lean_object* v_init_1967_, lean_object* v_start_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1966_, v_init_1967_, v_start_1968_);
lean_dec(v_start_1968_);
lean_dec_ref(v_t_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1973_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1970_, v___x_1972_, v___x_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_PersistentArray_toArray___redArg(v_t_1974_);
lean_dec_ref(v_t_1974_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1976_, lean_object* v_t_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_PersistentArray_toArray___redArg(v_t_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_t_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1979_, v_t_1980_);
lean_dec_ref(v_t_1980_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1982_, lean_object* v_t_1983_, lean_object* v_init_1984_, lean_object* v_start_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1983_, v_init_1984_, v_start_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_t_1988_, lean_object* v_init_1989_, lean_object* v_start_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1987_, v_t_1988_, v_init_1989_, v_start_1990_);
lean_dec(v_start_1990_);
lean_dec_ref(v_t_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1992_, lean_object* v_x_1993_, size_t v_x_1994_, size_t v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1993_, v_x_1994_, v_x_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
size_t v_x_1655__boxed_2003_; size_t v_x_1656__boxed_2004_; lean_object* v_res_2005_; 
v_x_1655__boxed_2003_ = lean_unbox_usize(v_x_2000_);
lean_dec(v_x_2000_);
v_x_1656__boxed_2004_ = lean_unbox_usize(v_x_2001_);
lean_dec(v_x_2001_);
v_res_2005_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1998_, v_x_1999_, v_x_1655__boxed_2003_, v_x_1656__boxed_2004_, v_x_2002_);
lean_dec_ref(v_x_1999_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_2006_, lean_object* v_as_2007_, size_t v_i_2008_, size_t v_stop_2009_, lean_object* v_b_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_2007_, v_i_2008_, v_stop_2009_, v_b_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_as_2013_, lean_object* v_i_2014_, lean_object* v_stop_2015_, lean_object* v_b_2016_){
_start:
{
size_t v_i_boxed_2017_; size_t v_stop_boxed_2018_; lean_object* v_res_2019_; 
v_i_boxed_2017_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_stop_boxed_2018_ = lean_unbox_usize(v_stop_2015_);
lean_dec(v_stop_2015_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_2012_, v_as_2013_, v_i_boxed_2017_, v_stop_boxed_2018_, v_b_2016_);
lean_dec_ref(v_as_2013_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_2021_, v_x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_2024_, v_x_2025_, v_x_2026_);
lean_dec_ref(v_x_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2028_, lean_object* v_as_2029_, size_t v_i_2030_, size_t v_stop_2031_, lean_object* v_b_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_2029_, v_i_2030_, v_stop_2031_, v_b_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2034_, lean_object* v_as_2035_, lean_object* v_i_2036_, lean_object* v_stop_2037_, lean_object* v_b_2038_){
_start:
{
size_t v_i_boxed_2039_; size_t v_stop_boxed_2040_; lean_object* v_res_2041_; 
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_stop_boxed_2040_ = lean_unbox_usize(v_stop_2037_);
lean_dec(v_stop_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_2034_, v_as_2035_, v_i_boxed_2039_, v_stop_boxed_2040_, v_b_2038_);
lean_dec_ref(v_as_2035_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_2042_, size_t v_i_2043_, size_t v_stop_2044_, lean_object* v_b_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_eq(v_i_2043_, v_stop_2044_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; 
v___x_2047_ = lean_array_uget_borrowed(v_as_2042_, v_i_2043_);
lean_inc(v___x_2047_);
v___x_2048_ = l_Lean_PersistentArray_push___redArg(v_b_2045_, v___x_2047_);
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2043_, v___x_2049_);
v_i_2043_ = v___x_2050_;
v_b_2045_ = v___x_2048_;
goto _start;
}
else
{
return v_b_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2052_, lean_object* v_i_2053_, lean_object* v_stop_2054_, lean_object* v_b_2055_){
_start:
{
size_t v_i_boxed_2056_; size_t v_stop_boxed_2057_; lean_object* v_res_2058_; 
v_i_boxed_2056_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_stop_boxed_2057_ = lean_unbox_usize(v_stop_2054_);
lean_dec(v_stop_2054_);
v_res_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2052_, v_i_boxed_2056_, v_stop_boxed_2057_, v_b_2055_);
lean_dec_ref(v_as_2052_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2059_, lean_object* v_x_2060_){
_start:
{
if (lean_obj_tag(v_x_2059_) == 0)
{
lean_object* v_cs_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_cs_2061_ = lean_ctor_get(v_x_2059_, 0);
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = lean_array_get_size(v_cs_2061_);
v___x_2064_ = lean_nat_dec_lt(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
return v_x_2060_;
}
else
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_nat_dec_le(v___x_2063_, v___x_2063_);
if (v___x_2065_ == 0)
{
if (v___x_2064_ == 0)
{
return v_x_2060_;
}
else
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = lean_usize_of_nat(v___x_2063_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2061_, v___x_2066_, v___x_2067_, v_x_2060_);
return v___x_2068_;
}
}
else
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = lean_usize_of_nat(v___x_2063_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2061_, v___x_2069_, v___x_2070_, v_x_2060_);
return v___x_2071_;
}
}
}
else
{
lean_object* v_vs_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_vs_2072_ = lean_ctor_get(v_x_2059_, 0);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_array_get_size(v_vs_2072_);
v___x_2075_ = lean_nat_dec_lt(v___x_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
return v_x_2060_;
}
else
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_nat_dec_le(v___x_2074_, v___x_2074_);
if (v___x_2076_ == 0)
{
if (v___x_2075_ == 0)
{
return v_x_2060_;
}
else
{
size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = ((size_t)0ULL);
v___x_2078_ = lean_usize_of_nat(v___x_2074_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2072_, v___x_2077_, v___x_2078_, v_x_2060_);
return v___x_2079_;
}
}
else
{
size_t v___x_2080_; size_t v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = ((size_t)0ULL);
v___x_2081_ = lean_usize_of_nat(v___x_2074_);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2072_, v___x_2080_, v___x_2081_, v_x_2060_);
return v___x_2082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2083_, size_t v_i_2084_, size_t v_stop_2085_, lean_object* v_b_2086_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_eq(v_i_2084_, v_stop_2085_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; 
v___x_2088_ = lean_array_uget_borrowed(v_as_2083_, v_i_2084_);
v___x_2089_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2088_, v_b_2086_);
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2084_, v___x_2090_);
v_i_2084_ = v___x_2091_;
v_b_2086_ = v___x_2089_;
goto _start;
}
else
{
return v_b_2086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2093_, lean_object* v_i_2094_, lean_object* v_stop_2095_, lean_object* v_b_2096_){
_start:
{
size_t v_i_boxed_2097_; size_t v_stop_boxed_2098_; lean_object* v_res_2099_; 
v_i_boxed_2097_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_stop_boxed_2098_ = lean_unbox_usize(v_stop_2095_);
lean_dec(v_stop_2095_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2093_, v_i_boxed_2097_, v_stop_boxed_2098_, v_b_2096_);
lean_dec_ref(v_as_2093_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2100_, lean_object* v_x_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2100_, v_x_2101_);
lean_dec_ref(v_x_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2103_, size_t v_x_2104_, size_t v_x_2105_, lean_object* v_x_2106_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_object* v_cs_2107_; lean_object* v___x_2108_; size_t v___x_2109_; lean_object* v_j_2110_; lean_object* v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_cs_2107_ = lean_ctor_get(v_x_2103_, 0);
v___x_2108_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2109_ = lean_usize_shift_right(v_x_2104_, v_x_2105_);
v_j_2110_ = lean_usize_to_nat(v___x_2109_);
v___x_2111_ = lean_array_get_borrowed(v___x_2108_, v_cs_2107_, v_j_2110_);
v___x_2112_ = ((size_t)1ULL);
v___x_2113_ = lean_usize_shift_left(v___x_2112_, v_x_2105_);
v___x_2114_ = lean_usize_sub(v___x_2113_, v___x_2112_);
v___x_2115_ = lean_usize_land(v_x_2104_, v___x_2114_);
v___x_2116_ = ((size_t)5ULL);
v___x_2117_ = lean_usize_sub(v_x_2105_, v___x_2116_);
v___x_2118_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2111_, v___x_2115_, v___x_2117_, v_x_2106_);
v___x_2119_ = lean_unsigned_to_nat(1u);
v___x_2120_ = lean_nat_add(v_j_2110_, v___x_2119_);
lean_dec(v_j_2110_);
v___x_2121_ = lean_array_get_size(v_cs_2107_);
v___x_2122_ = lean_nat_dec_lt(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec(v___x_2120_);
return v___x_2118_;
}
else
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_nat_dec_le(v___x_2121_, v___x_2121_);
if (v___x_2123_ == 0)
{
if (v___x_2122_ == 0)
{
lean_dec(v___x_2120_);
return v___x_2118_;
}
else
{
size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_usize_of_nat(v___x_2120_);
lean_dec(v___x_2120_);
v___x_2125_ = lean_usize_of_nat(v___x_2121_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2107_, v___x_2124_, v___x_2125_, v___x_2118_);
return v___x_2126_;
}
}
else
{
size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_usize_of_nat(v___x_2120_);
lean_dec(v___x_2120_);
v___x_2128_ = lean_usize_of_nat(v___x_2121_);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2107_, v___x_2127_, v___x_2128_, v___x_2118_);
return v___x_2129_;
}
}
}
else
{
lean_object* v_vs_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v_vs_2130_ = lean_ctor_get(v_x_2103_, 0);
v___x_2131_ = lean_usize_to_nat(v_x_2104_);
v___x_2132_ = lean_array_get_size(v_vs_2130_);
v___x_2133_ = lean_nat_dec_lt(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_dec(v___x_2131_);
return v_x_2106_;
}
else
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_nat_dec_le(v___x_2132_, v___x_2132_);
if (v___x_2134_ == 0)
{
if (v___x_2133_ == 0)
{
lean_dec(v___x_2131_);
return v_x_2106_;
}
else
{
size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_usize_of_nat(v___x_2131_);
lean_dec(v___x_2131_);
v___x_2136_ = lean_usize_of_nat(v___x_2132_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2130_, v___x_2135_, v___x_2136_, v_x_2106_);
return v___x_2137_;
}
}
else
{
size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_usize_of_nat(v___x_2131_);
lean_dec(v___x_2131_);
v___x_2139_ = lean_usize_of_nat(v___x_2132_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2130_, v___x_2138_, v___x_2139_, v_x_2106_);
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
size_t v_x_1523__boxed_2145_; size_t v_x_1524__boxed_2146_; lean_object* v_res_2147_; 
v_x_1523__boxed_2145_ = lean_unbox_usize(v_x_2142_);
lean_dec(v_x_2142_);
v_x_1524__boxed_2146_ = lean_unbox_usize(v_x_2143_);
lean_dec(v_x_2143_);
v_res_2147_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2141_, v_x_1523__boxed_2145_, v_x_1524__boxed_2146_, v_x_2144_);
lean_dec_ref(v_x_2141_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2148_, lean_object* v_init_2149_, lean_object* v_start_2150_){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = lean_unsigned_to_nat(0u);
v___x_2152_ = lean_nat_dec_eq(v_start_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v_root_2153_; lean_object* v_tail_2154_; size_t v_shift_2155_; lean_object* v_tailOff_2156_; uint8_t v___x_2157_; 
v_root_2153_ = lean_ctor_get(v_t_2148_, 0);
v_tail_2154_ = lean_ctor_get(v_t_2148_, 1);
v_shift_2155_ = lean_ctor_get_usize(v_t_2148_, 4);
v_tailOff_2156_ = lean_ctor_get(v_t_2148_, 3);
v___x_2157_ = lean_nat_dec_le(v_tailOff_2156_, v_start_2150_);
if (v___x_2157_ == 0)
{
size_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2158_ = lean_usize_of_nat(v_start_2150_);
v___x_2159_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2153_, v___x_2158_, v_shift_2155_, v_init_2149_);
v___x_2160_ = lean_array_get_size(v_tail_2154_);
v___x_2161_ = lean_nat_dec_lt(v___x_2151_, v___x_2160_);
if (v___x_2161_ == 0)
{
return v___x_2159_;
}
else
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_nat_dec_le(v___x_2160_, v___x_2160_);
if (v___x_2162_ == 0)
{
if (v___x_2161_ == 0)
{
return v___x_2159_;
}
else
{
size_t v___x_2163_; size_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = ((size_t)0ULL);
v___x_2164_ = lean_usize_of_nat(v___x_2160_);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2154_, v___x_2163_, v___x_2164_, v___x_2159_);
return v___x_2165_;
}
}
else
{
size_t v___x_2166_; size_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = lean_usize_of_nat(v___x_2160_);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2154_, v___x_2166_, v___x_2167_, v___x_2159_);
return v___x_2168_;
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2169_ = lean_nat_sub(v_start_2150_, v_tailOff_2156_);
v___x_2170_ = lean_array_get_size(v_tail_2154_);
v___x_2171_ = lean_nat_dec_lt(v___x_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_dec(v___x_2169_);
return v_init_2149_;
}
else
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_le(v___x_2170_, v___x_2170_);
if (v___x_2172_ == 0)
{
if (v___x_2171_ == 0)
{
lean_dec(v___x_2169_);
return v_init_2149_;
}
else
{
size_t v___x_2173_; size_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_usize_of_nat(v___x_2169_);
lean_dec(v___x_2169_);
v___x_2174_ = lean_usize_of_nat(v___x_2170_);
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2154_, v___x_2173_, v___x_2174_, v_init_2149_);
return v___x_2175_;
}
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_usize_of_nat(v___x_2169_);
lean_dec(v___x_2169_);
v___x_2177_ = lean_usize_of_nat(v___x_2170_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2154_, v___x_2176_, v___x_2177_, v_init_2149_);
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_root_2179_; lean_object* v_tail_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_root_2179_ = lean_ctor_get(v_t_2148_, 0);
v_tail_2180_ = lean_ctor_get(v_t_2148_, 1);
v___x_2181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2179_, v_init_2149_);
v___x_2182_ = lean_array_get_size(v_tail_2180_);
v___x_2183_ = lean_nat_dec_lt(v___x_2151_, v___x_2182_);
if (v___x_2183_ == 0)
{
return v___x_2181_;
}
else
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_nat_dec_le(v___x_2182_, v___x_2182_);
if (v___x_2184_ == 0)
{
if (v___x_2183_ == 0)
{
return v___x_2181_;
}
else
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = lean_usize_of_nat(v___x_2182_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2180_, v___x_2185_, v___x_2186_, v___x_2181_);
return v___x_2187_;
}
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = lean_usize_of_nat(v___x_2182_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2180_, v___x_2188_, v___x_2189_, v___x_2181_);
return v___x_2190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2191_, lean_object* v_init_2192_, lean_object* v_start_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2191_, v_init_2192_, v_start_2193_);
lean_dec(v_start_2193_);
lean_dec_ref(v_t_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2195_, lean_object* v_t_u2082_2196_){
_start:
{
uint8_t v___x_2197_; 
v___x_2197_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2195_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2196_, v_t_u2081_2195_, v___x_2198_);
return v___x_2199_;
}
else
{
lean_dec_ref(v_t_u2081_2195_);
lean_inc_ref(v_t_u2082_2196_);
return v_t_u2082_2196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2200_, lean_object* v_t_u2082_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2200_, v_t_u2082_2201_);
lean_dec_ref(v_t_u2082_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2203_, lean_object* v_t_u2081_2204_, lean_object* v_t_u2082_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2204_, v_t_u2082_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_t_u2081_2208_, lean_object* v_t_u2082_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_PersistentArray_append(v_00_u03b1_2207_, v_t_u2081_2208_, v_t_u2082_2209_);
lean_dec_ref(v_t_u2082_2209_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2211_, lean_object* v_t_2212_, lean_object* v_init_2213_, lean_object* v_start_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2212_, v_init_2213_, v_start_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_t_2217_, lean_object* v_init_2218_, lean_object* v_start_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2216_, v_t_2217_, v_init_2218_, v_start_2219_);
lean_dec(v_start_2219_);
lean_dec_ref(v_t_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2221_, lean_object* v_x_2222_, size_t v_x_2223_, size_t v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2222_, v_x_2223_, v_x_2224_, v_x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
size_t v_x_1679__boxed_2232_; size_t v_x_1680__boxed_2233_; lean_object* v_res_2234_; 
v_x_1679__boxed_2232_ = lean_unbox_usize(v_x_2229_);
lean_dec(v_x_2229_);
v_x_1680__boxed_2233_ = lean_unbox_usize(v_x_2230_);
lean_dec(v_x_2230_);
v_res_2234_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2227_, v_x_2228_, v_x_1679__boxed_2232_, v_x_1680__boxed_2233_, v_x_2231_);
lean_dec_ref(v_x_2228_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2235_, lean_object* v_as_2236_, size_t v_i_2237_, size_t v_stop_2238_, lean_object* v_b_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2236_, v_i_2237_, v_stop_2238_, v_b_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2241_, lean_object* v_as_2242_, lean_object* v_i_2243_, lean_object* v_stop_2244_, lean_object* v_b_2245_){
_start:
{
size_t v_i_boxed_2246_; size_t v_stop_boxed_2247_; lean_object* v_res_2248_; 
v_i_boxed_2246_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_stop_boxed_2247_ = lean_unbox_usize(v_stop_2244_);
lean_dec(v_stop_2244_);
v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2241_, v_as_2242_, v_i_boxed_2246_, v_stop_boxed_2247_, v_b_2245_);
lean_dec_ref(v_as_2242_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2250_, v_x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2253_, v_x_2254_, v_x_2255_);
lean_dec_ref(v_x_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2257_, lean_object* v_as_2258_, size_t v_i_2259_, size_t v_stop_2260_, lean_object* v_b_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2258_, v_i_2259_, v_stop_2260_, v_b_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_as_2264_, lean_object* v_i_2265_, lean_object* v_stop_2266_, lean_object* v_b_2267_){
_start:
{
size_t v_i_boxed_2268_; size_t v_stop_boxed_2269_; lean_object* v_res_2270_; 
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_stop_boxed_2269_ = lean_unbox_usize(v_stop_2266_);
lean_dec(v_stop_2266_);
v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2263_, v_as_2264_, v_i_boxed_2268_, v_stop_boxed_2269_, v_b_2267_);
lean_dec_ref(v_as_2264_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___closed__0));
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2274_, lean_object* v_x_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_apply_1(v_f_2274_, v_x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2277_, lean_object* v_f_2278_){
_start:
{
lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2279_, 0, v_f_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2281_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2280_, v_t_2277_, v___f_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2282_, lean_object* v_00_u03b2_2283_, lean_object* v_t_2284_, lean_object* v_f_2285_){
_start:
{
lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___f_2286_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2286_, 0, v_f_2285_);
v___x_2287_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2288_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2287_, v_t_2284_, v___f_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2289_, lean_object* v_f_2290_){
_start:
{
lean_object* v___f_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2291_, 0, v_f_2290_);
v___x_2292_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2293_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2292_, v_t_2289_, v___f_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2294_, lean_object* v_00_u03b2_2295_, lean_object* v_t_2296_, lean_object* v_f_2297_){
_start:
{
lean_object* v___f_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2298_, 0, v_f_2297_);
v___x_2299_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2300_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2299_, v_t_2296_, v___f_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2301_, size_t v_i_2302_, size_t v_stop_2303_, lean_object* v_b_2304_){
_start:
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_usize_dec_eq(v_i_2302_, v_stop_2303_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; 
v___x_2306_ = lean_array_uget_borrowed(v_as_2301_, v_i_2302_);
lean_inc(v___x_2306_);
v___x_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_b_2304_);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_add(v_i_2302_, v___x_2308_);
v_i_2302_ = v___x_2309_;
v_b_2304_ = v___x_2307_;
goto _start;
}
else
{
return v_b_2304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2311_, lean_object* v_i_2312_, lean_object* v_stop_2313_, lean_object* v_b_2314_){
_start:
{
size_t v_i_boxed_2315_; size_t v_stop_boxed_2316_; lean_object* v_res_2317_; 
v_i_boxed_2315_ = lean_unbox_usize(v_i_2312_);
lean_dec(v_i_2312_);
v_stop_boxed_2316_ = lean_unbox_usize(v_stop_2313_);
lean_dec(v_stop_2313_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2311_, v_i_boxed_2315_, v_stop_boxed_2316_, v_b_2314_);
lean_dec_ref(v_as_2311_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2318_, lean_object* v_x_2319_){
_start:
{
if (lean_obj_tag(v_x_2318_) == 0)
{
lean_object* v_cs_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_cs_2320_ = lean_ctor_get(v_x_2318_, 0);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_array_get_size(v_cs_2320_);
v___x_2323_ = lean_nat_dec_lt(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
return v_x_2319_;
}
else
{
uint8_t v___x_2324_; 
v___x_2324_ = lean_nat_dec_le(v___x_2322_, v___x_2322_);
if (v___x_2324_ == 0)
{
if (v___x_2323_ == 0)
{
return v_x_2319_;
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = lean_usize_of_nat(v___x_2322_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2320_, v___x_2325_, v___x_2326_, v_x_2319_);
return v___x_2327_;
}
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2322_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2320_, v___x_2328_, v___x_2329_, v_x_2319_);
return v___x_2330_;
}
}
}
else
{
lean_object* v_vs_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_vs_2331_ = lean_ctor_get(v_x_2318_, 0);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_get_size(v_vs_2331_);
v___x_2334_ = lean_nat_dec_lt(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
return v_x_2319_;
}
else
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_nat_dec_le(v___x_2333_, v___x_2333_);
if (v___x_2335_ == 0)
{
if (v___x_2334_ == 0)
{
return v_x_2319_;
}
else
{
size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = ((size_t)0ULL);
v___x_2337_ = lean_usize_of_nat(v___x_2333_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2331_, v___x_2336_, v___x_2337_, v_x_2319_);
return v___x_2338_;
}
}
else
{
size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = ((size_t)0ULL);
v___x_2340_ = lean_usize_of_nat(v___x_2333_);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2331_, v___x_2339_, v___x_2340_, v_x_2319_);
return v___x_2341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2342_, size_t v_i_2343_, size_t v_stop_2344_, lean_object* v_b_2345_){
_start:
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_usize_dec_eq(v_i_2343_, v_stop_2344_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; size_t v___x_2349_; size_t v___x_2350_; 
v___x_2347_ = lean_array_uget_borrowed(v_as_2342_, v_i_2343_);
v___x_2348_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2347_, v_b_2345_);
v___x_2349_ = ((size_t)1ULL);
v___x_2350_ = lean_usize_add(v_i_2343_, v___x_2349_);
v_i_2343_ = v___x_2350_;
v_b_2345_ = v___x_2348_;
goto _start;
}
else
{
return v_b_2345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2352_, lean_object* v_i_2353_, lean_object* v_stop_2354_, lean_object* v_b_2355_){
_start:
{
size_t v_i_boxed_2356_; size_t v_stop_boxed_2357_; lean_object* v_res_2358_; 
v_i_boxed_2356_ = lean_unbox_usize(v_i_2353_);
lean_dec(v_i_2353_);
v_stop_boxed_2357_ = lean_unbox_usize(v_stop_2354_);
lean_dec(v_stop_2354_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2352_, v_i_boxed_2356_, v_stop_boxed_2357_, v_b_2355_);
lean_dec_ref(v_as_2352_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2359_, lean_object* v_x_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2359_, v_x_2360_);
lean_dec_ref(v_x_2359_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2362_, size_t v_x_2363_, size_t v_x_2364_, lean_object* v_x_2365_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_object* v_cs_2366_; lean_object* v___x_2367_; size_t v___x_2368_; lean_object* v_j_2369_; lean_object* v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_cs_2366_ = lean_ctor_get(v_x_2362_, 0);
v___x_2367_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2368_ = lean_usize_shift_right(v_x_2363_, v_x_2364_);
v_j_2369_ = lean_usize_to_nat(v___x_2368_);
v___x_2370_ = lean_array_get_borrowed(v___x_2367_, v_cs_2366_, v_j_2369_);
v___x_2371_ = ((size_t)1ULL);
v___x_2372_ = lean_usize_shift_left(v___x_2371_, v_x_2364_);
v___x_2373_ = lean_usize_sub(v___x_2372_, v___x_2371_);
v___x_2374_ = lean_usize_land(v_x_2363_, v___x_2373_);
v___x_2375_ = ((size_t)5ULL);
v___x_2376_ = lean_usize_sub(v_x_2364_, v___x_2375_);
v___x_2377_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2370_, v___x_2374_, v___x_2376_, v_x_2365_);
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = lean_nat_add(v_j_2369_, v___x_2378_);
lean_dec(v_j_2369_);
v___x_2380_ = lean_array_get_size(v_cs_2366_);
v___x_2381_ = lean_nat_dec_lt(v___x_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_dec(v___x_2379_);
return v___x_2377_;
}
else
{
uint8_t v___x_2382_; 
v___x_2382_ = lean_nat_dec_le(v___x_2380_, v___x_2380_);
if (v___x_2382_ == 0)
{
if (v___x_2381_ == 0)
{
lean_dec(v___x_2379_);
return v___x_2377_;
}
else
{
size_t v___x_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = lean_usize_of_nat(v___x_2379_);
lean_dec(v___x_2379_);
v___x_2384_ = lean_usize_of_nat(v___x_2380_);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2366_, v___x_2383_, v___x_2384_, v___x_2377_);
return v___x_2385_;
}
}
else
{
size_t v___x_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_usize_of_nat(v___x_2379_);
lean_dec(v___x_2379_);
v___x_2387_ = lean_usize_of_nat(v___x_2380_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2366_, v___x_2386_, v___x_2387_, v___x_2377_);
return v___x_2388_;
}
}
}
else
{
lean_object* v_vs_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_vs_2389_ = lean_ctor_get(v_x_2362_, 0);
v___x_2390_ = lean_usize_to_nat(v_x_2363_);
v___x_2391_ = lean_array_get_size(v_vs_2389_);
v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_dec(v___x_2390_);
return v_x_2365_;
}
else
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_nat_dec_le(v___x_2391_, v___x_2391_);
if (v___x_2393_ == 0)
{
if (v___x_2392_ == 0)
{
lean_dec(v___x_2390_);
return v_x_2365_;
}
else
{
size_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_usize_of_nat(v___x_2390_);
lean_dec(v___x_2390_);
v___x_2395_ = lean_usize_of_nat(v___x_2391_);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2389_, v___x_2394_, v___x_2395_, v_x_2365_);
return v___x_2396_;
}
}
else
{
size_t v___x_2397_; size_t v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_usize_of_nat(v___x_2390_);
lean_dec(v___x_2390_);
v___x_2398_ = lean_usize_of_nat(v___x_2391_);
v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2389_, v___x_2397_, v___x_2398_, v_x_2365_);
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
size_t v_x_1497__boxed_2404_; size_t v_x_1498__boxed_2405_; lean_object* v_res_2406_; 
v_x_1497__boxed_2404_ = lean_unbox_usize(v_x_2401_);
lean_dec(v_x_2401_);
v_x_1498__boxed_2405_ = lean_unbox_usize(v_x_2402_);
lean_dec(v_x_2402_);
v_res_2406_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2400_, v_x_1497__boxed_2404_, v_x_1498__boxed_2405_, v_x_2403_);
lean_dec_ref(v_x_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2407_, lean_object* v_init_2408_, lean_object* v_start_2409_){
_start:
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = lean_nat_dec_eq(v_start_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v_root_2412_; lean_object* v_tail_2413_; size_t v_shift_2414_; lean_object* v_tailOff_2415_; uint8_t v___x_2416_; 
v_root_2412_ = lean_ctor_get(v_t_2407_, 0);
v_tail_2413_ = lean_ctor_get(v_t_2407_, 1);
v_shift_2414_ = lean_ctor_get_usize(v_t_2407_, 4);
v_tailOff_2415_ = lean_ctor_get(v_t_2407_, 3);
v___x_2416_ = lean_nat_dec_le(v_tailOff_2415_, v_start_2409_);
if (v___x_2416_ == 0)
{
size_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2417_ = lean_usize_of_nat(v_start_2409_);
v___x_2418_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2412_, v___x_2417_, v_shift_2414_, v_init_2408_);
v___x_2419_ = lean_array_get_size(v_tail_2413_);
v___x_2420_ = lean_nat_dec_lt(v___x_2410_, v___x_2419_);
if (v___x_2420_ == 0)
{
return v___x_2418_;
}
else
{
uint8_t v___x_2421_; 
v___x_2421_ = lean_nat_dec_le(v___x_2419_, v___x_2419_);
if (v___x_2421_ == 0)
{
if (v___x_2420_ == 0)
{
return v___x_2418_;
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2419_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2413_, v___x_2422_, v___x_2423_, v___x_2418_);
return v___x_2424_;
}
}
else
{
size_t v___x_2425_; size_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = ((size_t)0ULL);
v___x_2426_ = lean_usize_of_nat(v___x_2419_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2413_, v___x_2425_, v___x_2426_, v___x_2418_);
return v___x_2427_;
}
}
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2428_ = lean_nat_sub(v_start_2409_, v_tailOff_2415_);
v___x_2429_ = lean_array_get_size(v_tail_2413_);
v___x_2430_ = lean_nat_dec_lt(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_dec(v___x_2428_);
return v_init_2408_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = lean_nat_dec_le(v___x_2429_, v___x_2429_);
if (v___x_2431_ == 0)
{
if (v___x_2430_ == 0)
{
lean_dec(v___x_2428_);
return v_init_2408_;
}
else
{
size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = lean_usize_of_nat(v___x_2428_);
lean_dec(v___x_2428_);
v___x_2433_ = lean_usize_of_nat(v___x_2429_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2413_, v___x_2432_, v___x_2433_, v_init_2408_);
return v___x_2434_;
}
}
else
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_usize_of_nat(v___x_2428_);
lean_dec(v___x_2428_);
v___x_2436_ = lean_usize_of_nat(v___x_2429_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2413_, v___x_2435_, v___x_2436_, v_init_2408_);
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_root_2438_; lean_object* v_tail_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v_root_2438_ = lean_ctor_get(v_t_2407_, 0);
v_tail_2439_ = lean_ctor_get(v_t_2407_, 1);
v___x_2440_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2438_, v_init_2408_);
v___x_2441_ = lean_array_get_size(v_tail_2439_);
v___x_2442_ = lean_nat_dec_lt(v___x_2410_, v___x_2441_);
if (v___x_2442_ == 0)
{
return v___x_2440_;
}
else
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_nat_dec_le(v___x_2441_, v___x_2441_);
if (v___x_2443_ == 0)
{
if (v___x_2442_ == 0)
{
return v___x_2440_;
}
else
{
size_t v___x_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = ((size_t)0ULL);
v___x_2445_ = lean_usize_of_nat(v___x_2441_);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2439_, v___x_2444_, v___x_2445_, v___x_2440_);
return v___x_2446_;
}
}
else
{
size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = ((size_t)0ULL);
v___x_2448_ = lean_usize_of_nat(v___x_2441_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2439_, v___x_2447_, v___x_2448_, v___x_2440_);
return v___x_2449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2450_, lean_object* v_init_2451_, lean_object* v_start_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2450_, v_init_2451_, v_start_2452_);
lean_dec(v_start_2452_);
lean_dec_ref(v_t_2450_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2454_, v___x_2455_, v___x_2456_);
v___x_2458_ = l_List_reverse___redArg(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_PersistentArray_toList___redArg(v_t_2459_);
lean_dec_ref(v_t_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2461_, lean_object* v_t_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_PersistentArray_toList___redArg(v_t_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2464_, lean_object* v_t_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_PersistentArray_toList(v_00_u03b1_2464_, v_t_2465_);
lean_dec_ref(v_t_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2467_, lean_object* v_t_2468_, lean_object* v_init_2469_, lean_object* v_start_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2468_, v_init_2469_, v_start_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_t_2473_, lean_object* v_init_2474_, lean_object* v_start_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2472_, v_t_2473_, v_init_2474_, v_start_2475_);
lean_dec(v_start_2475_);
lean_dec_ref(v_t_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2477_, lean_object* v_x_2478_, size_t v_x_2479_, size_t v_x_2480_, lean_object* v_x_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2478_, v_x_2479_, v_x_2480_, v_x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
size_t v_x_1655__boxed_2488_; size_t v_x_1656__boxed_2489_; lean_object* v_res_2490_; 
v_x_1655__boxed_2488_ = lean_unbox_usize(v_x_2485_);
lean_dec(v_x_2485_);
v_x_1656__boxed_2489_ = lean_unbox_usize(v_x_2486_);
lean_dec(v_x_2486_);
v_res_2490_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2483_, v_x_2484_, v_x_1655__boxed_2488_, v_x_1656__boxed_2489_, v_x_2487_);
lean_dec_ref(v_x_2484_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2491_, lean_object* v_as_2492_, size_t v_i_2493_, size_t v_stop_2494_, lean_object* v_b_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2492_, v_i_2493_, v_stop_2494_, v_b_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_as_2498_, lean_object* v_i_2499_, lean_object* v_stop_2500_, lean_object* v_b_2501_){
_start:
{
size_t v_i_boxed_2502_; size_t v_stop_boxed_2503_; lean_object* v_res_2504_; 
v_i_boxed_2502_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_stop_boxed_2503_ = lean_unbox_usize(v_stop_2500_);
lean_dec(v_stop_2500_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2497_, v_as_2498_, v_i_boxed_2502_, v_stop_boxed_2503_, v_b_2501_);
lean_dec_ref(v_as_2498_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2506_, v_x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2509_, v_x_2510_, v_x_2511_);
lean_dec_ref(v_x_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2513_, lean_object* v_as_2514_, size_t v_i_2515_, size_t v_stop_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2514_, v_i_2515_, v_stop_2516_, v_b_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2519_, lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_stop_2522_, lean_object* v_b_2523_){
_start:
{
size_t v_i_boxed_2524_; size_t v_stop_boxed_2525_; lean_object* v_res_2526_; 
v_i_boxed_2524_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_stop_boxed_2525_ = lean_unbox_usize(v_stop_2522_);
lean_dec(v_stop_2522_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2519_, v_as_2520_, v_i_boxed_2524_, v_stop_boxed_2525_, v_b_2523_);
lean_dec_ref(v_as_2520_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2527_, lean_object* v_p_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2529_) == 0)
{
lean_object* v_cs_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_cs_2530_ = lean_ctor_get(v_x_2529_, 0);
lean_inc_ref(v_cs_2530_);
lean_dec_ref(v_x_2529_);
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_array_get_size(v_cs_2530_);
v___x_2533_ = lean_nat_dec_lt(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v_toApplicative_2534_; lean_object* v_toPure_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v_cs_2530_);
lean_dec(v_p_2528_);
v_toApplicative_2534_ = lean_ctor_get(v_inst_2527_, 0);
lean_inc_ref(v_toApplicative_2534_);
lean_dec_ref(v_inst_2527_);
v_toPure_2535_ = lean_ctor_get(v_toApplicative_2534_, 1);
lean_inc(v_toPure_2535_);
lean_dec_ref(v_toApplicative_2534_);
v___x_2536_ = lean_box(v___x_2533_);
v___x_2537_ = lean_apply_2(v_toPure_2535_, lean_box(0), v___x_2536_);
return v___x_2537_;
}
else
{
if (v___x_2533_ == 0)
{
lean_object* v_toApplicative_2538_; lean_object* v_toPure_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec_ref(v_cs_2530_);
lean_dec(v_p_2528_);
v_toApplicative_2538_ = lean_ctor_get(v_inst_2527_, 0);
lean_inc_ref(v_toApplicative_2538_);
lean_dec_ref(v_inst_2527_);
v_toPure_2539_ = lean_ctor_get(v_toApplicative_2538_, 1);
lean_inc(v_toPure_2539_);
lean_dec_ref(v_toApplicative_2538_);
v___x_2540_ = lean_box(v___x_2533_);
v___x_2541_ = lean_apply_2(v_toPure_2539_, lean_box(0), v___x_2540_);
return v___x_2541_;
}
else
{
lean_object* v___f_2542_; size_t v___x_2543_; size_t v___x_2544_; lean_object* v___x_2545_; 
lean_inc_ref(v_inst_2527_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2542_, 0, v_inst_2527_);
lean_closure_set(v___f_2542_, 1, v_p_2528_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = lean_usize_of_nat(v___x_2532_);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2527_, v___f_2542_, v_cs_2530_, v___x_2543_, v___x_2544_);
return v___x_2545_;
}
}
}
else
{
lean_object* v_vs_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_vs_2546_ = lean_ctor_get(v_x_2529_, 0);
lean_inc_ref(v_vs_2546_);
lean_dec_ref(v_x_2529_);
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_array_get_size(v_vs_2546_);
v___x_2549_ = lean_nat_dec_lt(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v_toApplicative_2550_; lean_object* v_toPure_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec_ref(v_vs_2546_);
lean_dec(v_p_2528_);
v_toApplicative_2550_ = lean_ctor_get(v_inst_2527_, 0);
lean_inc_ref(v_toApplicative_2550_);
lean_dec_ref(v_inst_2527_);
v_toPure_2551_ = lean_ctor_get(v_toApplicative_2550_, 1);
lean_inc(v_toPure_2551_);
lean_dec_ref(v_toApplicative_2550_);
v___x_2552_ = lean_box(v___x_2549_);
v___x_2553_ = lean_apply_2(v_toPure_2551_, lean_box(0), v___x_2552_);
return v___x_2553_;
}
else
{
if (v___x_2549_ == 0)
{
lean_object* v_toApplicative_2554_; lean_object* v_toPure_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec_ref(v_vs_2546_);
lean_dec(v_p_2528_);
v_toApplicative_2554_ = lean_ctor_get(v_inst_2527_, 0);
lean_inc_ref(v_toApplicative_2554_);
lean_dec_ref(v_inst_2527_);
v_toPure_2555_ = lean_ctor_get(v_toApplicative_2554_, 1);
lean_inc(v_toPure_2555_);
lean_dec_ref(v_toApplicative_2554_);
v___x_2556_ = lean_box(v___x_2549_);
v___x_2557_ = lean_apply_2(v_toPure_2555_, lean_box(0), v___x_2556_);
return v___x_2557_;
}
else
{
size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = lean_usize_of_nat(v___x_2548_);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2527_, v_p_2528_, v_vs_2546_, v___x_2558_, v___x_2559_);
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2561_, lean_object* v_p_2562_, lean_object* v_c_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2561_, v_p_2562_, v_c_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2565_, lean_object* v_m_2566_, lean_object* v_inst_2567_, lean_object* v_p_2568_, lean_object* v_x_2569_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2567_, v_p_2568_, v_x_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2571_, lean_object* v_toPure_2572_, lean_object* v_inst_2573_, lean_object* v_p_2574_, uint8_t v_b_2575_){
_start:
{
if (v_b_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_array_get_size(v_tail_2571_);
v___x_2578_ = lean_nat_dec_lt(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v_p_2574_);
lean_dec_ref(v_inst_2573_);
lean_dec_ref(v_tail_2571_);
v___x_2579_ = lean_box(v_b_2575_);
v___x_2580_ = lean_apply_2(v_toPure_2572_, lean_box(0), v___x_2579_);
return v___x_2580_;
}
else
{
if (v___x_2578_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec(v_p_2574_);
lean_dec_ref(v_inst_2573_);
lean_dec_ref(v_tail_2571_);
v___x_2581_ = lean_box(v_b_2575_);
v___x_2582_ = lean_apply_2(v_toPure_2572_, lean_box(0), v___x_2581_);
return v___x_2582_;
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v_toPure_2572_);
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2577_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2573_, v_p_2574_, v_tail_2571_, v___x_2583_, v___x_2584_);
return v___x_2585_;
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec(v_p_2574_);
lean_dec_ref(v_inst_2573_);
lean_dec_ref(v_tail_2571_);
v___x_2586_ = lean_box(v_b_2575_);
v___x_2587_ = lean_apply_2(v_toPure_2572_, lean_box(0), v___x_2586_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2588_, lean_object* v_toPure_2589_, lean_object* v_inst_2590_, lean_object* v_p_2591_, lean_object* v_b_2592_){
_start:
{
uint8_t v_b_boxed_2593_; lean_object* v_res_2594_; 
v_b_boxed_2593_ = lean_unbox(v_b_2592_);
v_res_2594_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2588_, v_toPure_2589_, v_inst_2590_, v_p_2591_, v_b_boxed_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2595_, lean_object* v_t_2596_, lean_object* v_p_2597_){
_start:
{
lean_object* v_toApplicative_2598_; lean_object* v_toBind_2599_; lean_object* v_root_2600_; lean_object* v_tail_2601_; lean_object* v_toPure_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; 
v_toApplicative_2598_ = lean_ctor_get(v_inst_2595_, 0);
v_toBind_2599_ = lean_ctor_get(v_inst_2595_, 1);
lean_inc(v_toBind_2599_);
v_root_2600_ = lean_ctor_get(v_t_2596_, 0);
lean_inc_ref(v_root_2600_);
v_tail_2601_ = lean_ctor_get(v_t_2596_, 1);
lean_inc_ref(v_tail_2601_);
lean_dec_ref(v_t_2596_);
v_toPure_2602_ = lean_ctor_get(v_toApplicative_2598_, 1);
lean_inc(v_toPure_2602_);
lean_inc(v_p_2597_);
lean_inc_ref(v_inst_2595_);
v___x_2603_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2595_, v_p_2597_, v_root_2600_);
v___f_2604_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2604_, 0, v_tail_2601_);
lean_closure_set(v___f_2604_, 1, v_toPure_2602_);
lean_closure_set(v___f_2604_, 2, v_inst_2595_);
lean_closure_set(v___f_2604_, 3, v_p_2597_);
v___x_2605_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2603_, v___f_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2606_, lean_object* v_m_2607_, lean_object* v_inst_2608_, lean_object* v_t_2609_, lean_object* v_p_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2608_, v_t_2609_, v_p_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2612_, uint8_t v_b_2613_){
_start:
{
if (v_b_2613_ == 0)
{
uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = 1;
v___x_2615_ = lean_box(v___x_2614_);
v___x_2616_ = lean_apply_2(v_toPure_2612_, lean_box(0), v___x_2615_);
return v___x_2616_;
}
else
{
uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = 0;
v___x_2618_ = lean_box(v___x_2617_);
v___x_2619_ = lean_apply_2(v_toPure_2612_, lean_box(0), v___x_2618_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2620_, lean_object* v_b_2621_){
_start:
{
uint8_t v_b_boxed_2622_; lean_object* v_res_2623_; 
v_b_boxed_2622_ = lean_unbox(v_b_2621_);
v_res_2623_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2620_, v_b_boxed_2622_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2624_, lean_object* v_toBind_2625_, lean_object* v___f_2626_, lean_object* v_v_2627_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_apply_1(v_p_2624_, v_v_2627_);
v___x_2629_ = lean_apply_4(v_toBind_2625_, lean_box(0), lean_box(0), v___x_2628_, v___f_2626_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2630_, lean_object* v_a_2631_, lean_object* v_p_2632_){
_start:
{
lean_object* v_toApplicative_2633_; lean_object* v_toBind_2634_; lean_object* v_toPure_2635_; lean_object* v___f_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_toApplicative_2633_ = lean_ctor_get(v_inst_2630_, 0);
v_toBind_2634_ = lean_ctor_get(v_inst_2630_, 1);
lean_inc_n(v_toBind_2634_, 2);
v_toPure_2635_ = lean_ctor_get(v_toApplicative_2633_, 1);
lean_inc(v_toPure_2635_);
v___f_2636_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2636_, 0, v_toPure_2635_);
lean_inc_ref(v___f_2636_);
v___f_2637_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2637_, 0, v_p_2632_);
lean_closure_set(v___f_2637_, 1, v_toBind_2634_);
lean_closure_set(v___f_2637_, 2, v___f_2636_);
v___x_2638_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2630_, v_a_2631_, v___f_2637_);
v___x_2639_ = lean_apply_4(v_toBind_2634_, lean_box(0), lean_box(0), v___x_2638_, v___f_2636_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2640_, lean_object* v_m_2641_, lean_object* v_inst_2642_, lean_object* v_a_2643_, lean_object* v_p_2644_){
_start:
{
lean_object* v_toApplicative_2645_; lean_object* v_toBind_2646_; lean_object* v_toPure_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_toApplicative_2645_ = lean_ctor_get(v_inst_2642_, 0);
v_toBind_2646_ = lean_ctor_get(v_inst_2642_, 1);
lean_inc_n(v_toBind_2646_, 2);
v_toPure_2647_ = lean_ctor_get(v_toApplicative_2645_, 1);
lean_inc(v_toPure_2647_);
v___f_2648_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2648_, 0, v_toPure_2647_);
lean_inc_ref(v___f_2648_);
v___f_2649_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2649_, 0, v_p_2644_);
lean_closure_set(v___f_2649_, 1, v_toBind_2646_);
lean_closure_set(v___f_2649_, 2, v___f_2648_);
v___x_2650_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2642_, v_a_2643_, v___f_2649_);
v___x_2651_ = lean_apply_4(v_toBind_2646_, lean_box(0), lean_box(0), v___x_2650_, v___f_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2652_, lean_object* v_x_2653_){
_start:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = lean_apply_1(v_p_2652_, v_x_2653_);
v___x_2655_ = lean_unbox(v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2656_, lean_object* v_x_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2656_, v_x_2657_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg(lean_object* v_a_2660_, lean_object* v_p_2661_){
_start:
{
lean_object* v___f_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2662_, 0, v_p_2661_);
v___x_2663_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2664_ = l_Lean_PersistentArray_anyM___redArg(v___x_2663_, v_a_2660_, v___f_2662_);
v___x_2665_ = lean_unbox(v___x_2664_);
lean_dec(v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___boxed(lean_object* v_a_2666_, lean_object* v_p_2667_){
_start:
{
uint8_t v_res_2668_; lean_object* v_r_2669_; 
v_res_2668_ = l_Lean_PersistentArray_any___redArg(v_a_2666_, v_p_2667_);
v_r_2669_ = lean_box(v_res_2668_);
return v_r_2669_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2670_, lean_object* v_a_2671_, lean_object* v_p_2672_){
_start:
{
lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2673_, 0, v_p_2672_);
v___x_2674_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2675_ = l_Lean_PersistentArray_anyM___redArg(v___x_2674_, v_a_2671_, v___f_2673_);
v___x_2676_ = lean_unbox(v___x_2675_);
lean_dec(v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_a_2678_, lean_object* v_p_2679_){
_start:
{
uint8_t v_res_2680_; lean_object* v_r_2681_; 
v_res_2680_ = l_Lean_PersistentArray_any(v_00_u03b1_2677_, v_a_2678_, v_p_2679_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2682_, lean_object* v_x_2683_){
_start:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = lean_apply_1(v_p_2682_, v_x_2683_);
v___x_2685_ = lean_unbox(v___x_2684_);
if (v___x_2685_ == 0)
{
uint8_t v___x_2686_; 
v___x_2686_ = 1;
return v___x_2686_;
}
else
{
uint8_t v___x_2687_; 
v___x_2687_ = 0;
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2688_, lean_object* v_x_2689_){
_start:
{
uint8_t v_res_2690_; lean_object* v_r_2691_; 
v_res_2690_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2688_, v_x_2689_);
v_r_2691_ = lean_box(v_res_2690_);
return v_r_2691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2692_, lean_object* v_p_2693_){
_start:
{
lean_object* v___f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___f_2694_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2694_, 0, v_p_2693_);
v___x_2695_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2696_ = l_Lean_PersistentArray_anyM___redArg(v___x_2695_, v_a_2692_, v___f_2694_);
v___x_2697_ = lean_unbox(v___x_2696_);
lean_dec(v___x_2696_);
if (v___x_2697_ == 0)
{
uint8_t v___x_2698_; 
v___x_2698_ = 1;
return v___x_2698_;
}
else
{
uint8_t v___x_2699_; 
v___x_2699_ = 0;
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2700_, lean_object* v_p_2701_){
_start:
{
uint8_t v_res_2702_; lean_object* v_r_2703_; 
v_res_2702_ = l_Lean_PersistentArray_all___redArg(v_a_2700_, v_p_2701_);
v_r_2703_ = lean_box(v_res_2702_);
return v_r_2703_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2704_, lean_object* v_a_2705_, lean_object* v_p_2706_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___f_2707_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2707_, 0, v_p_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2709_ = l_Lean_PersistentArray_anyM___redArg(v___x_2708_, v_a_2705_, v___f_2707_);
v___x_2710_ = lean_unbox(v___x_2709_);
lean_dec(v___x_2709_);
if (v___x_2710_ == 0)
{
uint8_t v___x_2711_; 
v___x_2711_ = 1;
return v___x_2711_;
}
else
{
uint8_t v___x_2712_; 
v___x_2712_ = 0;
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_a_2714_, lean_object* v_p_2715_){
_start:
{
uint8_t v_res_2716_; lean_object* v_r_2717_; 
v_res_2716_ = l_Lean_PersistentArray_all(v_00_u03b1_2713_, v_a_2714_, v_p_2715_);
v_r_2717_ = lean_box(v_res_2716_);
return v_r_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_cs_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_vs_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2724_, lean_object* v_f_2725_, lean_object* v_x_2726_){
_start:
{
if (lean_obj_tag(v_x_2726_) == 0)
{
lean_object* v_toApplicative_2727_; lean_object* v_toFunctor_2728_; lean_object* v_cs_2729_; lean_object* v_map_2730_; lean_object* v___f_2731_; lean_object* v___f_2732_; size_t v_sz_2733_; size_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_toApplicative_2727_ = lean_ctor_get(v_inst_2724_, 0);
v_toFunctor_2728_ = lean_ctor_get(v_toApplicative_2727_, 0);
v_cs_2729_ = lean_ctor_get(v_x_2726_, 0);
lean_inc_ref(v_cs_2729_);
lean_dec_ref(v_x_2726_);
v_map_2730_ = lean_ctor_get(v_toFunctor_2728_, 0);
lean_inc(v_map_2730_);
v___f_2731_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2724_);
v___f_2732_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2732_, 0, v_inst_2724_);
lean_closure_set(v___f_2732_, 1, v_f_2725_);
v_sz_2733_ = lean_array_size(v_cs_2729_);
v___x_2734_ = ((size_t)0ULL);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2724_, v___f_2732_, v_sz_2733_, v___x_2734_, v_cs_2729_);
v___x_2736_ = lean_apply_4(v_map_2730_, lean_box(0), lean_box(0), v___f_2731_, v___x_2735_);
return v___x_2736_;
}
else
{
lean_object* v_toApplicative_2737_; lean_object* v_toFunctor_2738_; lean_object* v_vs_2739_; lean_object* v_map_2740_; lean_object* v___f_2741_; size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_toApplicative_2737_ = lean_ctor_get(v_inst_2724_, 0);
v_toFunctor_2738_ = lean_ctor_get(v_toApplicative_2737_, 0);
v_vs_2739_ = lean_ctor_get(v_x_2726_, 0);
lean_inc_ref(v_vs_2739_);
lean_dec_ref(v_x_2726_);
v_map_2740_ = lean_ctor_get(v_toFunctor_2738_, 0);
lean_inc(v_map_2740_);
v___f_2741_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2742_ = lean_array_size(v_vs_2739_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2724_, v_f_2725_, v_sz_2742_, v___x_2743_, v_vs_2739_);
v___x_2745_ = lean_apply_4(v_map_2740_, lean_box(0), lean_box(0), v___f_2741_, v___x_2744_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2746_, lean_object* v_f_2747_, lean_object* v_c_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2746_, v_f_2747_, v_c_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2750_, lean_object* v_m_2751_, lean_object* v_inst_2752_, lean_object* v_00_u03b2_2753_, lean_object* v_f_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2752_, v_f_2754_, v_x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2757_, lean_object* v_size_2758_, size_t v_shift_2759_, lean_object* v_tailOff_2760_, lean_object* v_toPure_2761_, lean_object* v_tail_2762_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2763_, 0, v_root_2757_);
lean_ctor_set(v___x_2763_, 1, v_tail_2762_);
lean_ctor_set(v___x_2763_, 2, v_size_2758_);
lean_ctor_set(v___x_2763_, 3, v_tailOff_2760_);
lean_ctor_set_usize(v___x_2763_, 4, v_shift_2759_);
v___x_2764_ = lean_apply_2(v_toPure_2761_, lean_box(0), v___x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2765_, lean_object* v_size_2766_, lean_object* v_shift_2767_, lean_object* v_tailOff_2768_, lean_object* v_toPure_2769_, lean_object* v_tail_2770_){
_start:
{
size_t v_shift_boxed_2771_; lean_object* v_res_2772_; 
v_shift_boxed_2771_ = lean_unbox_usize(v_shift_2767_);
lean_dec(v_shift_2767_);
v_res_2772_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2765_, v_size_2766_, v_shift_boxed_2771_, v_tailOff_2768_, v_toPure_2769_, v_tail_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2773_, size_t v_shift_2774_, lean_object* v_tailOff_2775_, lean_object* v_toPure_2776_, lean_object* v_tail_2777_, lean_object* v_inst_2778_, lean_object* v_f_2779_, lean_object* v_toBind_2780_, lean_object* v_root_2781_){
_start:
{
lean_object* v___x_2782_; lean_object* v___f_2783_; size_t v_sz_2784_; size_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2782_ = lean_box_usize(v_shift_2774_);
v___f_2783_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2783_, 0, v_root_2781_);
lean_closure_set(v___f_2783_, 1, v_size_2773_);
lean_closure_set(v___f_2783_, 2, v___x_2782_);
lean_closure_set(v___f_2783_, 3, v_tailOff_2775_);
lean_closure_set(v___f_2783_, 4, v_toPure_2776_);
v_sz_2784_ = lean_array_size(v_tail_2777_);
v___x_2785_ = ((size_t)0ULL);
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2778_, v_f_2779_, v_sz_2784_, v___x_2785_, v_tail_2777_);
v___x_2787_ = lean_apply_4(v_toBind_2780_, lean_box(0), lean_box(0), v___x_2786_, v___f_2783_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2788_, lean_object* v_shift_2789_, lean_object* v_tailOff_2790_, lean_object* v_toPure_2791_, lean_object* v_tail_2792_, lean_object* v_inst_2793_, lean_object* v_f_2794_, lean_object* v_toBind_2795_, lean_object* v_root_2796_){
_start:
{
size_t v_shift_boxed_2797_; lean_object* v_res_2798_; 
v_shift_boxed_2797_ = lean_unbox_usize(v_shift_2789_);
lean_dec(v_shift_2789_);
v_res_2798_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2788_, v_shift_boxed_2797_, v_tailOff_2790_, v_toPure_2791_, v_tail_2792_, v_inst_2793_, v_f_2794_, v_toBind_2795_, v_root_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2799_, lean_object* v_f_2800_, lean_object* v_t_2801_){
_start:
{
lean_object* v_toApplicative_2802_; lean_object* v_toBind_2803_; lean_object* v_root_2804_; lean_object* v_tail_2805_; lean_object* v_size_2806_; size_t v_shift_2807_; lean_object* v_tailOff_2808_; lean_object* v_toPure_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___f_2812_; lean_object* v___x_2813_; 
v_toApplicative_2802_ = lean_ctor_get(v_inst_2799_, 0);
v_toBind_2803_ = lean_ctor_get(v_inst_2799_, 1);
lean_inc_n(v_toBind_2803_, 2);
v_root_2804_ = lean_ctor_get(v_t_2801_, 0);
lean_inc_ref(v_root_2804_);
v_tail_2805_ = lean_ctor_get(v_t_2801_, 1);
lean_inc_ref(v_tail_2805_);
v_size_2806_ = lean_ctor_get(v_t_2801_, 2);
lean_inc(v_size_2806_);
v_shift_2807_ = lean_ctor_get_usize(v_t_2801_, 4);
v_tailOff_2808_ = lean_ctor_get(v_t_2801_, 3);
lean_inc(v_tailOff_2808_);
lean_dec_ref(v_t_2801_);
v_toPure_2809_ = lean_ctor_get(v_toApplicative_2802_, 1);
lean_inc(v_toPure_2809_);
lean_inc(v_f_2800_);
lean_inc_ref(v_inst_2799_);
v___x_2810_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2799_, v_f_2800_, v_root_2804_);
v___x_2811_ = lean_box_usize(v_shift_2807_);
v___f_2812_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2812_, 0, v_size_2806_);
lean_closure_set(v___f_2812_, 1, v___x_2811_);
lean_closure_set(v___f_2812_, 2, v_tailOff_2808_);
lean_closure_set(v___f_2812_, 3, v_toPure_2809_);
lean_closure_set(v___f_2812_, 4, v_tail_2805_);
lean_closure_set(v___f_2812_, 5, v_inst_2799_);
lean_closure_set(v___f_2812_, 6, v_f_2800_);
lean_closure_set(v___f_2812_, 7, v_toBind_2803_);
v___x_2813_ = lean_apply_4(v_toBind_2803_, lean_box(0), lean_box(0), v___x_2810_, v___f_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2814_, lean_object* v_m_2815_, lean_object* v_inst_2816_, lean_object* v_00_u03b2_2817_, lean_object* v_f_2818_, lean_object* v_t_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2816_, v_f_2818_, v_t_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_apply_1(v_f_2821_, v_x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2824_, lean_object* v_t_2825_){
_start:
{
lean_object* v___f_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2826_, 0, v_f_2824_);
v___x_2827_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2828_ = l_Lean_PersistentArray_mapM___redArg(v___x_2827_, v___f_2826_, v_t_2825_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2829_, lean_object* v_00_u03b2_2830_, lean_object* v_f_2831_, lean_object* v_t_2832_){
_start:
{
lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___f_2833_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2833_, 0, v_f_2831_);
v___x_2834_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2835_ = l_Lean_PersistentArray_mapM___redArg(v___x_2834_, v___f_2833_, v_t_2832_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2836_) == 0)
{
lean_object* v_cs_2839_; lean_object* v_numNodes_2840_; lean_object* v_depth_2841_; lean_object* v_tailSize_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2864_; 
v_cs_2839_ = lean_ctor_get(v_x_2836_, 0);
v_numNodes_2840_ = lean_ctor_get(v_x_2837_, 0);
v_depth_2841_ = lean_ctor_get(v_x_2837_, 1);
v_tailSize_2842_ = lean_ctor_get(v_x_2837_, 2);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_x_2837_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2844_ = v_x_2837_;
v_isShared_2845_ = v_isSharedCheck_2864_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_tailSize_2842_);
lean_inc(v_depth_2841_);
lean_inc(v_numNodes_2840_);
lean_dec(v_x_2837_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2864_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___y_2849_; uint8_t v___x_2863_; 
v___x_2846_ = lean_unsigned_to_nat(1u);
v___x_2847_ = lean_nat_add(v_numNodes_2840_, v___x_2846_);
lean_dec(v_numNodes_2840_);
v___x_2863_ = lean_nat_dec_le(v_x_2838_, v_depth_2841_);
if (v___x_2863_ == 0)
{
lean_dec(v_depth_2841_);
lean_inc(v_x_2838_);
v___y_2849_ = v_x_2838_;
goto v___jp_2848_;
}
else
{
v___y_2849_ = v_depth_2841_;
goto v___jp_2848_;
}
v___jp_2848_:
{
lean_object* v___x_2851_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___y_2849_);
lean_ctor_set(v___x_2844_, 0, v___x_2847_);
v___x_2851_ = v___x_2844_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___y_2849_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_tailSize_2842_);
v___x_2851_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = lean_array_get_size(v_cs_2839_);
v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_dec(v_x_2838_);
return v___x_2851_;
}
else
{
uint8_t v___x_2855_; 
v___x_2855_ = lean_nat_dec_le(v___x_2853_, v___x_2853_);
if (v___x_2855_ == 0)
{
if (v___x_2854_ == 0)
{
lean_dec(v_x_2838_);
return v___x_2851_;
}
else
{
size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = ((size_t)0ULL);
v___x_2857_ = lean_usize_of_nat(v___x_2853_);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2838_, v_cs_2839_, v___x_2856_, v___x_2857_, v___x_2851_);
lean_dec(v_x_2838_);
return v___x_2858_;
}
}
else
{
size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = lean_usize_of_nat(v___x_2853_);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2838_, v_cs_2839_, v___x_2859_, v___x_2860_, v___x_2851_);
lean_dec(v_x_2838_);
return v___x_2861_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2865_; lean_object* v_depth_2866_; lean_object* v_tailSize_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2880_; 
v_numNodes_2865_ = lean_ctor_get(v_x_2837_, 0);
v_depth_2866_ = lean_ctor_get(v_x_2837_, 1);
v_tailSize_2867_ = lean_ctor_get(v_x_2837_, 2);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_x_2837_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2869_ = v_x_2837_;
v_isShared_2870_ = v_isSharedCheck_2880_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_tailSize_2867_);
lean_inc(v_depth_2866_);
lean_inc(v_numNodes_2865_);
lean_dec(v_x_2837_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2880_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = lean_nat_add(v_numNodes_2865_, v___x_2871_);
lean_dec(v_numNodes_2865_);
v___x_2873_ = lean_nat_dec_le(v_x_2838_, v_depth_2866_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2875_; 
lean_dec(v_depth_2866_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v_x_2838_);
lean_ctor_set(v___x_2869_, 0, v___x_2872_);
v___x_2875_ = v___x_2869_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_x_2838_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_tailSize_2867_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
else
{
lean_object* v___x_2878_; 
lean_dec(v_x_2838_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2872_);
v___x_2878_ = v___x_2869_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_depth_2866_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_tailSize_2867_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2881_, lean_object* v_as_2882_, size_t v_i_2883_, size_t v_stop_2884_, lean_object* v_b_2885_){
_start:
{
uint8_t v___x_2886_; 
v___x_2886_ = lean_usize_dec_eq(v_i_2883_, v_stop_2884_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; 
v___x_2887_ = lean_array_uget_borrowed(v_as_2882_, v_i_2883_);
v___x_2888_ = lean_unsigned_to_nat(1u);
v___x_2889_ = lean_nat_add(v_x_2881_, v___x_2888_);
v___x_2890_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2887_, v_b_2885_, v___x_2889_);
v___x_2891_ = ((size_t)1ULL);
v___x_2892_ = lean_usize_add(v_i_2883_, v___x_2891_);
v_i_2883_ = v___x_2892_;
v_b_2885_ = v___x_2890_;
goto _start;
}
else
{
return v_b_2885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2894_, lean_object* v_as_2895_, lean_object* v_i_2896_, lean_object* v_stop_2897_, lean_object* v_b_2898_){
_start:
{
size_t v_i_boxed_2899_; size_t v_stop_boxed_2900_; lean_object* v_res_2901_; 
v_i_boxed_2899_ = lean_unbox_usize(v_i_2896_);
lean_dec(v_i_2896_);
v_stop_boxed_2900_ = lean_unbox_usize(v_stop_2897_);
lean_dec(v_stop_2897_);
v_res_2901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2894_, v_as_2895_, v_i_boxed_2899_, v_stop_boxed_2900_, v_b_2898_);
lean_dec_ref(v_as_2895_);
lean_dec(v_x_2894_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2902_, v_x_2903_, v_x_2904_);
lean_dec_ref(v_x_2902_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_, lean_object* v_x_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2907_, v_x_2908_, v_x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2911_, v_x_2912_, v_x_2913_, v_x_2914_);
lean_dec_ref(v_x_2912_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2916_, lean_object* v_x_2917_, lean_object* v_as_2918_, size_t v_i_2919_, size_t v_stop_2920_, lean_object* v_b_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2917_, v_as_2918_, v_i_2919_, v_stop_2920_, v_b_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2923_, lean_object* v_x_2924_, lean_object* v_as_2925_, lean_object* v_i_2926_, lean_object* v_stop_2927_, lean_object* v_b_2928_){
_start:
{
size_t v_i_boxed_2929_; size_t v_stop_boxed_2930_; lean_object* v_res_2931_; 
v_i_boxed_2929_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_stop_boxed_2930_ = lean_unbox_usize(v_stop_2927_);
lean_dec(v_stop_2927_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2923_, v_x_2924_, v_as_2925_, v_i_boxed_2929_, v_stop_boxed_2930_, v_b_2928_);
lean_dec_ref(v_as_2925_);
lean_dec(v_x_2924_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2932_){
_start:
{
lean_object* v_root_2933_; lean_object* v_tail_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_root_2933_ = lean_ctor_get(v_r_2932_, 0);
v_tail_2934_ = lean_ctor_get(v_r_2932_, 1);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_array_get_size(v_tail_2934_);
v___x_2937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2935_);
lean_ctor_set(v___x_2937_, 2, v___x_2936_);
v___x_2938_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2933_, v___x_2937_, v___x_2935_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_PersistentArray_stats___redArg(v_r_2939_);
lean_dec_ref(v_r_2939_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2941_, lean_object* v_r_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_PersistentArray_stats___redArg(v_r_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2944_, lean_object* v_r_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_PersistentArray_stats(v_00_u03b1_2944_, v_r_2945_);
lean_dec_ref(v_r_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2951_){
_start:
{
lean_object* v_numNodes_2952_; lean_object* v_depth_2953_; lean_object* v_tailSize_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_numNodes_2952_ = lean_ctor_get(v_s_2951_, 0);
lean_inc(v_numNodes_2952_);
v_depth_2953_ = lean_ctor_get(v_s_2951_, 1);
lean_inc(v_depth_2953_);
v_tailSize_2954_ = lean_ctor_get(v_s_2951_, 2);
lean_inc(v_tailSize_2954_);
lean_dec_ref(v_s_2951_);
v___x_2955_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2956_ = l_Nat_reprFast(v_numNodes_2952_);
v___x_2957_ = lean_string_append(v___x_2955_, v___x_2956_);
lean_dec_ref(v___x_2956_);
v___x_2958_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2959_ = lean_string_append(v___x_2957_, v___x_2958_);
v___x_2960_ = l_Nat_reprFast(v_depth_2953_);
v___x_2961_ = lean_string_append(v___x_2959_, v___x_2960_);
lean_dec_ref(v___x_2960_);
v___x_2962_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2963_ = lean_string_append(v___x_2961_, v___x_2962_);
v___x_2964_ = l_Nat_reprFast(v_tailSize_2954_);
v___x_2965_ = lean_string_append(v___x_2963_, v___x_2964_);
lean_dec_ref(v___x_2964_);
v___x_2966_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2967_ = lean_string_append(v___x_2965_, v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2970_, lean_object* v_j_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_zero_2973_; uint8_t v_isZero_2974_; 
v_zero_2973_ = lean_unsigned_to_nat(0u);
v_isZero_2974_ = lean_nat_dec_eq(v_j_2971_, v_zero_2973_);
if (v_isZero_2974_ == 1)
{
lean_dec(v_j_2971_);
lean_dec(v_v_2970_);
return v_a_2972_;
}
else
{
lean_object* v_one_2975_; lean_object* v_n_2976_; lean_object* v___x_2977_; 
v_one_2975_ = lean_unsigned_to_nat(1u);
v_n_2976_ = lean_nat_sub(v_j_2971_, v_one_2975_);
lean_dec(v_j_2971_);
lean_inc(v_v_2970_);
v___x_2977_ = l_Lean_PersistentArray_push___redArg(v_a_2972_, v_v_2970_);
v_j_2971_ = v_n_2976_;
v_a_2972_ = v___x_2977_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_mkPersistentArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_PersistentArray_empty(lean_box(0));
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2980_, lean_object* v_v_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_2983_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2981_, v_n_2980_, v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2984_, lean_object* v_n_2985_, lean_object* v_v_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_mkPersistentArray___redArg(v_n_2985_, v_v_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2988_, lean_object* v_v_2989_, lean_object* v_n_2990_, lean_object* v_j_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2989_, v_j_2991_, v_a_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2995_, lean_object* v_v_2996_, lean_object* v_n_2997_, lean_object* v_j_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2995_, v_v_2996_, v_n_2997_, v_j_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_n_2997_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_3002_, lean_object* v_v_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_mkPersistentArray___redArg(v_n_3002_, v_v_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_3005_, lean_object* v_n_3006_, lean_object* v_v_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_mkPersistentArray___redArg(v_n_3006_, v_v_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
if (lean_obj_tag(v_a_3009_) == 0)
{
return v_a_3010_;
}
else
{
lean_object* v_head_3011_; lean_object* v_tail_3012_; lean_object* v___x_3013_; 
v_head_3011_ = lean_ctor_get(v_a_3009_, 0);
lean_inc(v_head_3011_);
v_tail_3012_ = lean_ctor_get(v_a_3009_, 1);
lean_inc(v_tail_3012_);
lean_dec_ref(v_a_3009_);
v___x_3013_ = l_Lean_PersistentArray_push___redArg(v_a_3010_, v_head_3011_);
v_a_3009_ = v_tail_3012_;
v_a_3010_ = v___x_3013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop(lean_object* v_00_u03b1_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(v_a_3016_, v_a_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_List_toPArray_x27___redArg(lean_object* v_xs_3019_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3020_ = lean_unsigned_to_nat(32u);
v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_3020_);
lean_dec_ref(v___x_3021_);
v___x_3022_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_3023_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(v_xs_3019_, v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_List_toPArray_x27(lean_object* v_00_u03b1_3024_, lean_object* v_xs_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_List_toPArray_x27___redArg(v_xs_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg(lean_object* v_xs_3027_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3028_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_array_get_size(v_xs_3027_);
v___x_3031_ = lean_nat_dec_lt(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
return v___x_3028_;
}
else
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_nat_dec_le(v___x_3030_, v___x_3030_);
if (v___x_3032_ == 0)
{
if (v___x_3031_ == 0)
{
return v___x_3028_;
}
else
{
size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = lean_usize_of_nat(v___x_3030_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_3027_, v___x_3033_, v___x_3034_, v___x_3028_);
return v___x_3035_;
}
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3030_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_3027_, v___x_3036_, v___x_3037_, v___x_3028_);
return v___x_3038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Array_toPArray_x27___redArg(v_xs_3039_);
lean_dec_ref(v_xs_3039_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27(lean_object* v_00_u03b1_3041_, lean_object* v_xs_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Array_toPArray_x27___redArg(v_xs_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_3044_, lean_object* v_xs_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Array_toPArray_x27(v_00_u03b1_3044_, v_xs_3045_);
lean_dec_ref(v_xs_3045_);
return v_res_3046_;
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
