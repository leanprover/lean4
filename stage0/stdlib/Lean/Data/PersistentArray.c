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
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg(){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__1));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg___boxed(lean_object* v___dummy_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v_res_55_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object* v_00_u03b1_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg(){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg___boxed(lean_object* v___dummy_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_instInhabitedPersistentArrayNode___redArg();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode___redArg(lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 1;
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___redArg___boxed(lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_68_);
lean_dec_ref(v_x_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode(lean_object* v_00_u03b1_71_, lean_object* v_x_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___boxed(lean_object* v_00_u03b1_74_, lean_object* v_x_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lean_PersistentArrayNode_isNode(v_00_u03b1_74_, v_x_75_);
lean_dec_ref(v_x_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
static size_t _init_l_Lean_PersistentArray_initShift(void){
_start:
{
size_t v___x_78_; 
v___x_78_ = ((size_t)5ULL);
return v___x_78_;
}
}
static size_t _init_l_Lean_PersistentArray_branching(void){
_start:
{
size_t v___x_79_; 
v___x_79_ = ((size_t)32ULL);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(32u);
v___x_81_ = lean_mk_empty_array_with_capacity(v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1(void){
_start:
{
size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_83_ = ((size_t)5ULL);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_unsigned_to_nat(32u);
v___x_86_ = lean_mk_empty_array_with_capacity(v___x_85_);
v___x_87_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__0, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__0);
v___x_88_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_84_);
lean_ctor_set(v___x_88_, 3, v___x_84_);
lean_ctor_set_usize(v___x_88_, 4, v___x_83_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg(){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg___boxed(lean_object* v___dummy_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v_res_92_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___closed__0(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object* v_00_u03b1_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg(){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg___boxed(lean_object* v___dummy_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_instInhabitedPersistentArray___redArg();
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object* v_a_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg(){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(32u);
v___x_104_ = lean_mk_empty_array_with_capacity(v___x_103_);
lean_dec_ref(v___x_104_);
v___x_105_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg___boxed(lean_object* v___dummy_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_PersistentArray_empty___redArg();
return v_res_107_;
}
}
static lean_object* _init_l_Lean_PersistentArray_empty___closed__0(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentArray_empty___redArg();
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object* v_00_u03b1_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
return v___x_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object* v_a_111_){
_start:
{
lean_object* v_size_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_size_112_ = lean_ctor_get(v_a_111_, 2);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_dec_eq(v_size_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object* v_a_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_115_);
lean_dec_ref(v_a_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty(lean_object* v_00_u03b1_118_, lean_object* v_a_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object* v_00_u03b1_121_, lean_object* v_a_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_121_, v_a_122_);
lean_dec_ref(v_a_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg(){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(32u);
v___x_127_ = lean_mk_empty_array_with_capacity(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg___boxed(lean_object* v___dummy_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
return v_res_129_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkEmptyArray___closed__0(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray(lean_object* v_00_u03b1_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
return v___x_132_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mul2Shift(size_t v_i_133_, size_t v_shift_134_){
_start:
{
size_t v___x_135_; 
v___x_135_ = lean_usize_shift_left(v_i_133_, v_shift_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mul2Shift___boxed(lean_object* v_i_136_, lean_object* v_shift_137_){
_start:
{
size_t v_i_boxed_138_; size_t v_shift_boxed_139_; size_t v_res_140_; lean_object* v_r_141_; 
v_i_boxed_138_ = lean_unbox_usize(v_i_136_);
lean_dec(v_i_136_);
v_shift_boxed_139_ = lean_unbox_usize(v_shift_137_);
lean_dec(v_shift_137_);
v_res_140_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_138_, v_shift_boxed_139_);
v_r_141_ = lean_box_usize(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_div2Shift(size_t v_i_142_, size_t v_shift_143_){
_start:
{
size_t v___x_144_; 
v___x_144_ = lean_usize_shift_right(v_i_142_, v_shift_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_div2Shift___boxed(lean_object* v_i_145_, lean_object* v_shift_146_){
_start:
{
size_t v_i_boxed_147_; size_t v_shift_boxed_148_; size_t v_res_149_; lean_object* v_r_150_; 
v_i_boxed_147_ = lean_unbox_usize(v_i_145_);
lean_dec(v_i_145_);
v_shift_boxed_148_ = lean_unbox_usize(v_shift_146_);
lean_dec(v_shift_146_);
v_res_149_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_147_, v_shift_boxed_148_);
v_r_150_ = lean_box_usize(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mod2Shift(size_t v_i_151_, size_t v_shift_152_){
_start:
{
size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; 
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_shift_left(v___x_153_, v_shift_152_);
v___x_155_ = lean_usize_sub(v___x_154_, v___x_153_);
v___x_156_ = lean_usize_land(v_i_151_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mod2Shift___boxed(lean_object* v_i_157_, lean_object* v_shift_158_){
_start:
{
size_t v_i_boxed_159_; size_t v_shift_boxed_160_; size_t v_res_161_; lean_object* v_r_162_; 
v_i_boxed_159_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_shift_boxed_160_ = lean_unbox_usize(v_shift_158_);
lean_dec(v_shift_158_);
v_res_161_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_159_, v_shift_boxed_160_);
v_r_162_ = lean_box_usize(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg(lean_object* v_inst_163_, lean_object* v_x_164_, size_t v_x_165_, size_t v_x_166_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v_cs_167_; lean_object* v___x_168_; size_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; 
v_cs_167_ = lean_ctor_get(v_x_164_, 0);
v___x_168_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_169_ = lean_usize_shift_right(v_x_165_, v_x_166_);
v___x_170_ = lean_usize_to_nat(v___x_169_);
v___x_171_ = lean_array_get_borrowed(v___x_168_, v_cs_167_, v___x_170_);
lean_dec(v___x_170_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_shift_left(v___x_172_, v_x_166_);
v___x_174_ = lean_usize_sub(v___x_173_, v___x_172_);
v___x_175_ = lean_usize_land(v_x_165_, v___x_174_);
v___x_176_ = ((size_t)5ULL);
v___x_177_ = lean_usize_sub(v_x_166_, v___x_176_);
v_x_164_ = v___x_171_;
v_x_165_ = v___x_175_;
v_x_166_ = v___x_177_;
goto _start;
}
else
{
lean_object* v_vs_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_vs_179_ = lean_ctor_get(v_x_164_, 0);
v___x_180_ = lean_usize_to_nat(v_x_165_);
v___x_181_ = lean_array_get_borrowed(v_inst_163_, v_vs_179_, v___x_180_);
lean_dec(v___x_180_);
lean_inc(v___x_181_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg___boxed(lean_object* v_inst_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
size_t v_x_94__boxed_186_; size_t v_x_95__boxed_187_; lean_object* v_res_188_; 
v_x_94__boxed_186_ = lean_unbox_usize(v_x_184_);
lean_dec(v_x_184_);
v_x_95__boxed_187_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_res_188_ = l_Lean_PersistentArray_getAux___redArg(v_inst_182_, v_x_183_, v_x_94__boxed_186_, v_x_95__boxed_187_);
lean_dec_ref(v_x_183_);
lean_dec(v_inst_182_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux(lean_object* v_00_u03b1_189_, lean_object* v_inst_190_, lean_object* v_x_191_, size_t v_x_192_, size_t v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_PersistentArray_getAux___redArg(v_inst_190_, v_x_191_, v_x_192_, v_x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___boxed(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
size_t v_x_136__boxed_200_; size_t v_x_137__boxed_201_; lean_object* v_res_202_; 
v_x_136__boxed_200_ = lean_unbox_usize(v_x_198_);
lean_dec(v_x_198_);
v_x_137__boxed_201_ = lean_unbox_usize(v_x_199_);
lean_dec(v_x_199_);
v_res_202_ = l_Lean_PersistentArray_getAux(v_00_u03b1_195_, v_inst_196_, v_x_197_, v_x_136__boxed_200_, v_x_137__boxed_201_);
lean_dec_ref(v_x_197_);
lean_dec(v_inst_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object* v_inst_203_, lean_object* v_t_204_, lean_object* v_i_205_){
_start:
{
lean_object* v_root_206_; lean_object* v_tail_207_; size_t v_shift_208_; lean_object* v_tailOff_209_; uint8_t v___x_210_; 
v_root_206_ = lean_ctor_get(v_t_204_, 0);
v_tail_207_ = lean_ctor_get(v_t_204_, 1);
v_shift_208_ = lean_ctor_get_usize(v_t_204_, 4);
v_tailOff_209_ = lean_ctor_get(v_t_204_, 3);
v___x_210_ = lean_nat_dec_le(v_tailOff_209_, v_i_205_);
if (v___x_210_ == 0)
{
size_t v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_usize_of_nat(v_i_205_);
v___x_212_ = l_Lean_PersistentArray_getAux___redArg(v_inst_203_, v_root_206_, v___x_211_, v_shift_208_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_nat_sub(v_i_205_, v_tailOff_209_);
v___x_214_ = lean_array_get_borrowed(v_inst_203_, v_tail_207_, v___x_213_);
lean_dec(v___x_213_);
lean_inc(v___x_214_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg___boxed(lean_object* v_inst_215_, lean_object* v_t_216_, lean_object* v_i_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_215_, v_t_216_, v_i_217_);
lean_dec(v_i_217_);
lean_dec_ref(v_t_216_);
lean_dec(v_inst_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_t_221_, lean_object* v_i_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_220_, v_t_221_, v_i_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___boxed(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_t_226_, lean_object* v_i_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_PersistentArray_get_x21(v_00_u03b1_224_, v_inst_225_, v_t_226_, v_i_227_);
lean_dec(v_i_227_);
lean_dec_ref(v_t_226_);
lean_dec(v_inst_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(lean_object* v_inst_229_, lean_object* v_xs_230_, lean_object* v_i_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_229_, v_xs_230_, v_i_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(lean_object* v_inst_234_, lean_object* v_xs_235_, lean_object* v_i_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(v_inst_234_, v_xs_235_, v_i_236_, v_x_237_);
lean_dec(v_i_236_);
lean_dec_ref(v_xs_235_);
lean_dec(v_inst_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(lean_object* v_inst_239_){
_start:
{
lean_object* v___f_240_; 
v___f_240_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_240_, 0, v_inst_239_);
return v___f_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(lean_object* v_00_u03b1_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_243_, 0, v_inst_242_);
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg(lean_object* v_x_244_, size_t v_x_245_, size_t v_x_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v_cs_248_; size_t v_j_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_cs_248_ = lean_ctor_get(v_x_244_, 0);
v_j_249_ = lean_usize_shift_right(v_x_245_, v_x_246_);
v___x_250_ = lean_usize_to_nat(v_j_249_);
v___x_251_ = lean_array_get_size(v_cs_248_);
v___x_252_ = lean_nat_dec_lt(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v___x_250_);
lean_dec(v_x_247_);
return v_x_244_;
}
else
{
lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_270_; 
lean_inc_ref(v_cs_248_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v_x_244_, 0);
lean_dec(v_unused_271_);
v___x_254_ = v_x_244_;
v_isShared_255_ = v_isSharedCheck_270_;
goto v_resetjp_253_;
}
else
{
lean_dec(v_x_244_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_270_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v_i_259_; size_t v___x_260_; size_t v_shift_261_; lean_object* v_v_262_; lean_object* v___x_263_; lean_object* v_xs_x27_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_shift_left(v___x_256_, v_x_246_);
v___x_258_ = lean_usize_sub(v___x_257_, v___x_256_);
v_i_259_ = lean_usize_land(v_x_245_, v___x_258_);
v___x_260_ = ((size_t)5ULL);
v_shift_261_ = lean_usize_sub(v_x_246_, v___x_260_);
v_v_262_ = lean_array_fget(v_cs_248_, v___x_250_);
v___x_263_ = lean_box(0);
v_xs_x27_264_ = lean_array_fset(v_cs_248_, v___x_250_, v___x_263_);
v___x_265_ = l_Lean_PersistentArray_setAux___redArg(v_v_262_, v_i_259_, v_shift_261_, v_x_247_);
v___x_266_ = lean_array_fset(v_xs_x27_264_, v___x_250_, v___x_265_);
lean_dec(v___x_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_266_);
v___x_268_ = v___x_254_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_vs_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_281_; 
v_vs_272_ = lean_ctor_get(v_x_244_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_281_ == 0)
{
v___x_274_ = v_x_244_;
v_isShared_275_ = v_isSharedCheck_281_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_vs_272_);
lean_dec(v_x_244_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_281_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_usize_to_nat(v_x_245_);
v___x_277_ = lean_array_set(v_vs_272_, v___x_276_, v_x_247_);
lean_dec(v___x_276_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg___boxed(lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
size_t v_x_79__boxed_286_; size_t v_x_80__boxed_287_; lean_object* v_res_288_; 
v_x_79__boxed_286_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_80__boxed_287_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_288_ = l_Lean_PersistentArray_setAux___redArg(v_x_282_, v_x_79__boxed_286_, v_x_80__boxed_287_, v_x_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux(lean_object* v_00_u03b1_289_, lean_object* v_x_290_, size_t v_x_291_, size_t v_x_292_, lean_object* v_x_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_PersistentArray_setAux___redArg(v_x_290_, v_x_291_, v_x_292_, v_x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___boxed(lean_object* v_00_u03b1_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
size_t v_x_149__boxed_300_; size_t v_x_150__boxed_301_; lean_object* v_res_302_; 
v_x_149__boxed_300_ = lean_unbox_usize(v_x_297_);
lean_dec(v_x_297_);
v_x_150__boxed_301_ = lean_unbox_usize(v_x_298_);
lean_dec(v_x_298_);
v_res_302_ = l_Lean_PersistentArray_setAux(v_00_u03b1_295_, v_x_296_, v_x_149__boxed_300_, v_x_150__boxed_301_, v_x_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg(lean_object* v_t_303_, lean_object* v_i_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_root_306_; lean_object* v_tail_307_; lean_object* v_size_308_; size_t v_shift_309_; lean_object* v_tailOff_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_325_; 
v_root_306_ = lean_ctor_get(v_t_303_, 0);
v_tail_307_ = lean_ctor_get(v_t_303_, 1);
v_size_308_ = lean_ctor_get(v_t_303_, 2);
v_shift_309_ = lean_ctor_get_usize(v_t_303_, 4);
v_tailOff_310_ = lean_ctor_get(v_t_303_, 3);
v_isSharedCheck_325_ = !lean_is_exclusive(v_t_303_);
if (v_isSharedCheck_325_ == 0)
{
v___x_312_ = v_t_303_;
v_isShared_313_ = v_isSharedCheck_325_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_tailOff_310_);
lean_inc(v_size_308_);
lean_inc(v_tail_307_);
lean_inc(v_root_306_);
lean_dec(v_t_303_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_325_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; 
v___x_314_ = lean_nat_dec_le(v_tailOff_310_, v_i_304_);
if (v___x_314_ == 0)
{
size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_315_ = lean_usize_of_nat(v_i_304_);
v___x_316_ = l_Lean_PersistentArray_setAux___redArg(v_root_306_, v___x_315_, v_shift_309_, v_a_305_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_316_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_tail_307_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_size_308_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_tailOff_310_);
lean_ctor_set_usize(v_reuseFailAlloc_319_, 4, v_shift_309_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = lean_nat_sub(v_i_304_, v_tailOff_310_);
v___x_321_ = lean_array_set(v_tail_307_, v___x_320_, v_a_305_);
lean_dec(v___x_320_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_321_);
v___x_323_ = v___x_312_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_root_306_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_size_308_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_tailOff_310_);
lean_ctor_set_usize(v_reuseFailAlloc_324_, 4, v_shift_309_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg___boxed(lean_object* v_t_326_, lean_object* v_i_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_PersistentArray_set___redArg(v_t_326_, v_i_327_, v_a_328_);
lean_dec(v_i_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set(lean_object* v_00_u03b1_330_, lean_object* v_t_331_, lean_object* v_i_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_PersistentArray_set___redArg(v_t_331_, v_i_332_, v_a_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___boxed(lean_object* v_00_u03b1_335_, lean_object* v_t_336_, lean_object* v_i_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_PersistentArray_set(v_00_u03b1_335_, v_t_336_, v_i_337_, v_a_338_);
lean_dec(v_i_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg(lean_object* v_f_340_, lean_object* v_x_341_, size_t v_x_342_, size_t v_x_343_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v_cs_344_; size_t v_j_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_cs_344_ = lean_ctor_get(v_x_341_, 0);
v_j_345_ = lean_usize_shift_right(v_x_342_, v_x_343_);
v___x_346_ = lean_usize_to_nat(v_j_345_);
v___x_347_ = lean_array_get_size(v_cs_344_);
v___x_348_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec(v___x_346_);
lean_dec(v_f_340_);
return v_x_341_;
}
else
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_cs_344_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_x_341_, 0);
lean_dec(v_unused_367_);
v___x_350_ = v_x_341_;
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
else
{
lean_dec(v_x_341_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v_i_355_; size_t v___x_356_; size_t v_shift_357_; lean_object* v_v_358_; lean_object* v___x_359_; lean_object* v_xs_x27_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_shift_left(v___x_352_, v_x_343_);
v___x_354_ = lean_usize_sub(v___x_353_, v___x_352_);
v_i_355_ = lean_usize_land(v_x_342_, v___x_354_);
v___x_356_ = ((size_t)5ULL);
v_shift_357_ = lean_usize_sub(v_x_343_, v___x_356_);
v_v_358_ = lean_array_fget(v_cs_344_, v___x_346_);
v___x_359_ = lean_box(0);
v_xs_x27_360_ = lean_array_fset(v_cs_344_, v___x_346_, v___x_359_);
v___x_361_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_340_, v_v_358_, v_i_355_, v_shift_357_);
v___x_362_ = lean_array_fset(v_xs_x27_360_, v___x_346_, v___x_361_);
lean_dec(v___x_346_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_362_);
v___x_364_ = v___x_350_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_vs_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_vs_368_ = lean_ctor_get(v_x_341_, 0);
v___x_369_ = lean_usize_to_nat(v_x_342_);
v___x_370_ = lean_array_get_size(v_vs_368_);
v___x_371_ = lean_nat_dec_lt(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec(v___x_369_);
lean_dec(v_f_340_);
return v_x_341_;
}
else
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_383_; 
lean_inc_ref(v_vs_368_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_x_341_, 0);
lean_dec(v_unused_384_);
v___x_373_ = v_x_341_;
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
else
{
lean_dec(v_x_341_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_v_375_; lean_object* v___x_376_; lean_object* v_xs_x27_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v_v_375_ = lean_array_fget(v_vs_368_, v___x_369_);
v___x_376_ = lean_box(0);
v_xs_x27_377_ = lean_array_fset(v_vs_368_, v___x_369_, v___x_376_);
v___x_378_ = lean_apply_1(v_f_340_, v_v_375_);
v___x_379_ = lean_array_fset(v_xs_x27_377_, v___x_369_, v___x_378_);
lean_dec(v___x_369_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_379_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg___boxed(lean_object* v_f_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
size_t v_x_96__boxed_389_; size_t v_x_97__boxed_390_; lean_object* v_res_391_; 
v_x_96__boxed_389_ = lean_unbox_usize(v_x_387_);
lean_dec(v_x_387_);
v_x_97__boxed_390_ = lean_unbox_usize(v_x_388_);
lean_dec(v_x_388_);
v_res_391_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_385_, v_x_386_, v_x_96__boxed_389_, v_x_97__boxed_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux(lean_object* v_00_u03b1_392_, lean_object* v_inst_393_, lean_object* v_f_394_, lean_object* v_x_395_, size_t v_x_396_, size_t v_x_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_394_, v_x_395_, v_x_396_, v_x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___boxed(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_f_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
size_t v_x_174__boxed_405_; size_t v_x_175__boxed_406_; lean_object* v_res_407_; 
v_x_174__boxed_405_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_x_175__boxed_406_ = lean_unbox_usize(v_x_404_);
lean_dec(v_x_404_);
v_res_407_ = l_Lean_PersistentArray_modifyAux(v_00_u03b1_399_, v_inst_400_, v_f_401_, v_x_402_, v_x_174__boxed_405_, v_x_175__boxed_406_);
lean_dec(v_inst_400_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg(lean_object* v_t_408_, lean_object* v_i_409_, lean_object* v_f_410_){
_start:
{
lean_object* v_root_411_; lean_object* v_tail_412_; lean_object* v_size_413_; size_t v_shift_414_; lean_object* v_tailOff_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_439_; 
v_root_411_ = lean_ctor_get(v_t_408_, 0);
v_tail_412_ = lean_ctor_get(v_t_408_, 1);
v_size_413_ = lean_ctor_get(v_t_408_, 2);
v_shift_414_ = lean_ctor_get_usize(v_t_408_, 4);
v_tailOff_415_ = lean_ctor_get(v_t_408_, 3);
v_isSharedCheck_439_ = !lean_is_exclusive(v_t_408_);
if (v_isSharedCheck_439_ == 0)
{
v___x_417_ = v_t_408_;
v_isShared_418_ = v_isSharedCheck_439_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_tailOff_415_);
lean_inc(v_size_413_);
lean_inc(v_tail_412_);
lean_inc(v_root_411_);
lean_dec(v_t_408_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_439_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_le(v_tailOff_415_, v_i_409_);
if (v___x_419_ == 0)
{
size_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_usize_of_nat(v_i_409_);
v___x_421_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_410_, v_root_411_, v___x_420_, v_shift_414_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_tail_412_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_size_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_tailOff_415_);
lean_ctor_set_usize(v_reuseFailAlloc_424_, 4, v_shift_414_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_nat_sub(v_i_409_, v_tailOff_415_);
v___x_426_ = lean_array_get_size(v_tail_412_);
v___x_427_ = lean_nat_dec_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v___x_425_);
lean_dec(v_f_410_);
if (v_isShared_418_ == 0)
{
v___x_429_ = v___x_417_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_root_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_tail_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_size_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_tailOff_415_);
lean_ctor_set_usize(v_reuseFailAlloc_430_, 4, v_shift_414_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v_v_431_; lean_object* v___x_432_; lean_object* v_xs_x27_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v_v_431_ = lean_array_fget(v_tail_412_, v___x_425_);
v___x_432_ = lean_box(0);
v_xs_x27_433_ = lean_array_fset(v_tail_412_, v___x_425_, v___x_432_);
v___x_434_ = lean_apply_1(v_f_410_, v_v_431_);
v___x_435_ = lean_array_fset(v_xs_x27_433_, v___x_425_, v___x_434_);
lean_dec(v___x_425_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_435_);
v___x_437_ = v___x_417_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_root_411_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_size_413_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_tailOff_415_);
lean_ctor_set_usize(v_reuseFailAlloc_438_, 4, v_shift_414_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg___boxed(lean_object* v_t_440_, lean_object* v_i_441_, lean_object* v_f_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_PersistentArray_modify___redArg(v_t_440_, v_i_441_, v_f_442_);
lean_dec(v_i_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify(lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_t_446_, lean_object* v_i_447_, lean_object* v_f_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentArray_modify___redArg(v_t_446_, v_i_447_, v_f_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___boxed(lean_object* v_00_u03b1_450_, lean_object* v_inst_451_, lean_object* v_t_452_, lean_object* v_i_453_, lean_object* v_f_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_PersistentArray_modify(v_00_u03b1_450_, v_inst_451_, v_t_452_, v_i_453_, v_f_454_);
lean_dec(v_i_453_);
lean_dec(v_inst_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t v_shift_456_, lean_object* v_a_457_){
_start:
{
size_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((size_t)0ULL);
v___x_459_ = lean_usize_dec_eq(v_shift_456_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; size_t v___x_461_; size_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_460_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v___x_461_ = ((size_t)5ULL);
v___x_462_ = lean_usize_sub(v_shift_456_, v___x_461_);
v___x_463_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_462_, v_a_457_);
v___x_464_ = lean_array_push(v___x_460_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_a_457_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg___boxed(lean_object* v_shift_467_, lean_object* v_a_468_){
_start:
{
size_t v_shift_boxed_469_; lean_object* v_res_470_; 
v_shift_boxed_469_ = lean_unbox_usize(v_shift_467_);
lean_dec(v_shift_467_);
v_res_470_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_469_, v_a_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath(lean_object* v_00_u03b1_471_, size_t v_shift_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_472_, v_a_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___boxed(lean_object* v_00_u03b1_475_, lean_object* v_shift_476_, lean_object* v_a_477_){
_start:
{
size_t v_shift_boxed_478_; lean_object* v_res_479_; 
v_shift_boxed_478_ = lean_unbox_usize(v_shift_476_);
lean_dec(v_shift_476_);
v_res_479_ = l_Lean_PersistentArray_mkNewPath(v_00_u03b1_475_, v_shift_boxed_478_, v_a_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object* v_x_480_, size_t v_x_481_, size_t v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_cs_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_cs_484_ = lean_ctor_get(v_x_480_, 0);
v___x_485_ = ((size_t)32ULL);
v___x_486_ = lean_usize_dec_lt(v_x_481_, v___x_485_);
if (v___x_486_ == 0)
{
size_t v_j_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v_shift_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_j_487_ = lean_usize_shift_right(v_x_481_, v_x_482_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_shift_left(v___x_488_, v_x_482_);
v___x_490_ = ((size_t)5ULL);
v_shift_491_ = lean_usize_sub(v_x_482_, v___x_490_);
v___x_492_ = lean_usize_to_nat(v_j_487_);
v___x_493_ = lean_array_get_size(v_cs_484_);
v___x_494_ = lean_nat_dec_lt(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
lean_inc_ref(v_cs_484_);
lean_dec(v___x_492_);
v_isSharedCheck_503_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_x_480_, 0);
lean_dec(v_unused_504_);
v___x_496_ = v_x_480_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_480_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_491_, v_x_483_);
v___x_499_ = lean_array_push(v_cs_484_, v___x_498_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
if (v___x_494_ == 0)
{
lean_dec(v___x_492_);
lean_dec_ref(v_x_483_);
return v_x_480_;
}
else
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_518_; 
lean_inc_ref(v_cs_484_);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_x_480_, 0);
lean_dec(v_unused_519_);
v___x_506_ = v_x_480_;
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_x_480_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
size_t v___x_508_; size_t v_i_509_; lean_object* v_v_510_; lean_object* v___x_511_; lean_object* v_xs_x27_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_508_ = lean_usize_sub(v___x_489_, v___x_488_);
v_i_509_ = lean_usize_land(v_x_481_, v___x_508_);
v_v_510_ = lean_array_fget(v_cs_484_, v___x_492_);
v___x_511_ = lean_box(0);
v_xs_x27_512_ = lean_array_fset(v_cs_484_, v___x_492_, v___x_511_);
v___x_513_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_v_510_, v_i_509_, v_shift_491_, v_x_483_);
v___x_514_ = lean_array_fset(v_xs_x27_512_, v___x_492_, v___x_513_);
lean_dec(v___x_492_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_514_);
v___x_516_ = v___x_506_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
lean_inc_ref(v_cs_484_);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_x_480_, 0);
lean_dec(v_unused_529_);
v___x_521_ = v_x_480_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_x_480_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 1);
lean_ctor_set(v___x_521_, 0, v_x_483_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_x_483_);
v___x_524_ = v_reuseFailAlloc_527_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_array_push(v_cs_484_, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
}
}
else
{
lean_dec_ref(v_x_483_);
return v_x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
size_t v_x_102__boxed_534_; size_t v_x_103__boxed_535_; lean_object* v_res_536_; 
v_x_102__boxed_534_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_x_103__boxed_535_ = lean_unbox_usize(v_x_532_);
lean_dec(v_x_532_);
v_res_536_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_530_, v_x_102__boxed_534_, v_x_103__boxed_535_, v_x_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object* v_00_u03b1_537_, lean_object* v_x_538_, size_t v_x_539_, size_t v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_538_, v_x_539_, v_x_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object* v_00_u03b1_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
size_t v_x_196__boxed_548_; size_t v_x_197__boxed_549_; lean_object* v_res_550_; 
v_x_196__boxed_548_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_x_197__boxed_549_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_550_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_543_, v_x_544_, v_x_196__boxed_548_, v_x_197__boxed_549_, v_x_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object* v_t_553_){
_start:
{
lean_object* v_root_554_; lean_object* v_tail_555_; lean_object* v_size_556_; size_t v_shift_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_584_; 
v_root_554_ = lean_ctor_get(v_t_553_, 0);
v_tail_555_ = lean_ctor_get(v_t_553_, 1);
v_size_556_ = lean_ctor_get(v_t_553_, 2);
v_shift_557_ = lean_ctor_get_usize(v_t_553_, 4);
v_isSharedCheck_584_ = !lean_is_exclusive(v_t_553_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_t_553_, 3);
lean_dec(v_unused_585_);
v___x_559_ = v_t_553_;
v_isShared_560_ = v_isSharedCheck_584_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_size_556_);
lean_inc(v_tail_555_);
lean_inc(v_root_554_);
lean_dec(v_t_553_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_584_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = ((size_t)5ULL);
v___x_563_ = lean_usize_add(v_shift_557_, v___x_562_);
v___x_564_ = lean_usize_shift_left(v___x_561_, v___x_563_);
v___x_565_ = lean_usize_to_nat(v___x_564_);
v___x_566_ = lean_nat_dec_le(v_size_556_, v___x_565_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v_n_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_567_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v_n_568_ = lean_array_push(v___x_567_, v_root_554_);
v___x_569_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_557_, v_tail_555_);
v___x_570_ = lean_array_push(v_n_568_, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
lean_inc(v_size_556_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 3, v_size_556_);
lean_ctor_set(v___x_559_, 1, v___x_572_);
lean_ctor_set(v___x_559_, 0, v___x_571_);
v___x_574_ = v___x_559_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_size_556_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_size_556_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_ctor_set_usize(v___x_574_, 4, v___x_563_);
return v___x_574_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; size_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_sub(v_size_556_, v___x_576_);
v___x_578_ = lean_usize_of_nat(v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_root_554_, v___x_578_, v_shift_557_, v_tail_555_);
v___x_580_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
lean_inc(v_size_556_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 3, v_size_556_);
lean_ctor_set(v___x_559_, 1, v___x_580_);
lean_ctor_set(v___x_559_, 0, v___x_579_);
v___x_582_ = v___x_559_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_size_556_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_size_556_);
lean_ctor_set_usize(v_reuseFailAlloc_583_, 4, v_shift_557_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object* v_00_u03b1_586_, lean_object* v_t_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_587_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__0(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = l_System_Platform_numBits;
v___x_590_ = lean_unsigned_to_nat(2u);
v___x_591_ = lean_nat_pow(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__1(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_unsigned_to_nat(3u);
v___x_593_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__0, &l_Lean_PersistentArray_tooBig___closed__0_once, _init_l_Lean_PersistentArray_tooBig___closed__0);
v___x_594_ = lean_nat_shiftr(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__1, &l_Lean_PersistentArray_tooBig___closed__1_once, _init_l_Lean_PersistentArray_tooBig___closed__1);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object* v_t_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_root_598_; lean_object* v_tail_599_; lean_object* v_size_600_; size_t v_shift_601_; lean_object* v_tailOff_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_618_; 
v_root_598_ = lean_ctor_get(v_t_596_, 0);
v_tail_599_ = lean_ctor_get(v_t_596_, 1);
v_size_600_ = lean_ctor_get(v_t_596_, 2);
v_shift_601_ = lean_ctor_get_usize(v_t_596_, 4);
v_tailOff_602_ = lean_ctor_get(v_t_596_, 3);
v_isSharedCheck_618_ = !lean_is_exclusive(v_t_596_);
if (v_isSharedCheck_618_ == 0)
{
v___x_604_ = v_t_596_;
v_isShared_605_ = v_isSharedCheck_618_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_tailOff_602_);
lean_inc(v_size_600_);
lean_inc(v_tail_599_);
lean_inc(v_root_598_);
lean_dec(v_t_596_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_618_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_r_610_; 
v___x_606_ = lean_array_push(v_tail_599_, v_a_597_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_size_600_, v___x_607_);
lean_inc_ref(v___x_606_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v___x_608_);
lean_ctor_set(v___x_604_, 1, v___x_606_);
v_r_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_root_598_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_tailOff_602_);
lean_ctor_set_usize(v_reuseFailAlloc_617_, 4, v_shift_601_);
v_r_610_ = v_reuseFailAlloc_617_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_array_get_size(v___x_606_);
lean_dec_ref(v___x_606_);
v___x_612_ = lean_unsigned_to_nat(32u);
v___x_613_ = lean_nat_dec_lt(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = l_Lean_PersistentArray_tooBig;
v___x_615_ = lean_nat_dec_le(v___x_614_, v_size_600_);
lean_dec(v_size_600_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_610_);
return v___x_616_;
}
else
{
return v_r_610_;
}
}
else
{
lean_dec(v_size_600_);
return v_r_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_619_, lean_object* v_t_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentArray_push___redArg(v_t_620_, v_a_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg(){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(32u);
v___x_625_ = lean_mk_empty_array_with_capacity(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg___boxed(lean_object* v___dummy_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v_res_627_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v_cs_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_685_; 
v_cs_635_ = lean_ctor_get(v_x_634_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_685_ == 0)
{
v___x_637_ = v_x_634_;
v_isShared_638_ = v_isSharedCheck_685_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_cs_635_);
lean_dec(v_x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_685_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_array_get_size(v_cs_635_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v_idx_643_; lean_object* v_last_644_; lean_object* v___x_645_; lean_object* v_fst_646_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v_idx_643_ = lean_nat_sub(v___x_639_, v___x_642_);
v_last_644_ = lean_array_fget_borrowed(v_cs_635_, v_idx_643_);
lean_inc(v_last_644_);
v___x_645_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_644_);
v_fst_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_646_);
if (lean_obj_tag(v_fst_646_) == 0)
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_idx_643_);
lean_del_object(v___x_637_);
lean_dec_ref(v_cs_635_);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_655_ = lean_ctor_get(v___x_645_, 1);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v___x_645_, 0);
lean_dec(v_unused_656_);
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_646_);
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
else
{
lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_682_; 
v_snd_657_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_645_, 0);
lean_dec(v_unused_683_);
v___x_659_ = v___x_645_;
v_isShared_660_ = v_isSharedCheck_682_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_dec(v___x_645_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_682_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v_cs_x27_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_661_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v_cs_x27_662_ = lean_array_fset(v_cs_635_, v_idx_643_, v___x_661_);
v___x_663_ = lean_array_get_size(v_snd_657_);
v___x_664_ = lean_nat_dec_eq(v___x_663_, v___x_640_);
if (v___x_664_ == 0)
{
lean_object* v___x_666_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v_snd_657_);
v___x_666_ = v___x_637_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_snd_657_);
v___x_666_ = v_reuseFailAlloc_671_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_array_fset(v_cs_x27_662_, v_idx_643_, v___x_666_);
lean_dec(v_idx_643_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_667_);
v___x_669_ = v___x_659_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_646_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_cs_x27_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
lean_dec(v_snd_657_);
lean_dec(v_idx_643_);
lean_del_object(v___x_637_);
v_cs_x27_672_ = lean_array_pop(v_cs_x27_662_);
v___x_673_ = lean_array_get_size(v_cs_x27_672_);
v___x_674_ = lean_nat_dec_eq(v___x_673_, v___x_640_);
if (v___x_674_ == 0)
{
lean_object* v___x_676_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v_cs_x27_672_);
v___x_676_ = v___x_659_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fst_646_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_cs_x27_672_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec_ref(v_cs_x27_672_);
v___x_678_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_678_);
v___x_680_ = v___x_659_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_fst_646_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
else
{
lean_object* v___x_684_; 
lean_del_object(v___x_637_);
lean_dec_ref(v_cs_635_);
v___x_684_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
return v___x_684_;
}
}
}
else
{
lean_object* v_vs_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_vs_686_ = lean_ctor_get(v_x_634_, 0);
lean_inc_ref(v_vs_686_);
lean_dec_ref_known(v_x_634_, 1);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_vs_686_);
v___x_688_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_690_, lean_object* v_x_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_693_){
_start:
{
lean_object* v_root_694_; lean_object* v_tail_695_; lean_object* v_size_696_; size_t v_shift_697_; lean_object* v_tailOff_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_root_694_ = lean_ctor_get(v_t_693_, 0);
v_tail_695_ = lean_ctor_get(v_t_693_, 1);
v_size_696_ = lean_ctor_get(v_t_693_, 2);
v_shift_697_ = lean_ctor_get_usize(v_t_693_, 4);
v_tailOff_698_ = lean_ctor_get(v_t_693_, 3);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_array_get_size(v_tail_695_);
v___x_701_ = lean_nat_dec_lt(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v_fst_703_; 
lean_inc_ref(v_root_694_);
v___x_702_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_694_);
v_fst_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_fst_703_);
if (lean_obj_tag(v_fst_703_) == 0)
{
lean_dec_ref(v___x_702_);
return v_t_693_;
}
else
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_736_; 
lean_inc(v_size_696_);
v_isSharedCheck_736_ = !lean_is_exclusive(v_t_693_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_737_ = lean_ctor_get(v_t_693_, 3);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_t_693_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_t_693_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_t_693_, 0);
lean_dec(v_unused_740_);
v___x_705_ = v_t_693_;
v_isShared_706_ = v_isSharedCheck_736_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_t_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_736_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_snd_707_; lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_735_; 
v_snd_707_ = lean_ctor_get(v___x_702_, 1);
lean_inc(v_snd_707_);
lean_dec_ref(v___x_702_);
v_val_708_ = lean_ctor_get(v_fst_703_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_fst_703_);
if (v_isSharedCheck_735_ == 0)
{
v___x_710_ = v_fst_703_;
v_isShared_711_ = v_isSharedCheck_735_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v_fst_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_735_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_last_712_; lean_object* v___x_713_; lean_object* v_newSize_714_; lean_object* v___x_715_; lean_object* v_newTailOff_716_; uint8_t v___y_718_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_last_712_ = lean_array_pop(v_val_708_);
v___x_713_ = lean_unsigned_to_nat(1u);
v_newSize_714_ = lean_nat_sub(v_size_696_, v___x_713_);
lean_dec(v_size_696_);
v___x_715_ = lean_array_get_size(v_last_712_);
v_newTailOff_716_ = lean_nat_sub(v_newSize_714_, v___x_715_);
v___x_731_ = lean_array_get_size(v_snd_707_);
v___x_732_ = lean_nat_dec_eq(v___x_731_, v___x_713_);
if (v___x_732_ == 0)
{
v___y_718_ = v___x_732_;
goto v___jp_717_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_array_fget_borrowed(v_snd_707_, v___x_699_);
v___x_734_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_733_);
v___y_718_ = v___x_734_;
goto v___jp_717_;
}
v___jp_717_:
{
if (v___y_718_ == 0)
{
lean_object* v___x_720_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 0);
lean_ctor_set(v___x_710_, 0, v_snd_707_);
v___x_720_ = v___x_710_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_snd_707_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 3, v_newTailOff_716_);
lean_ctor_set(v___x_705_, 2, v_newSize_714_);
lean_ctor_set(v___x_705_, 1, v_last_712_);
lean_ctor_set(v___x_705_, 0, v___x_720_);
v___x_722_ = v___x_705_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_last_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_newSize_714_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_newTailOff_716_);
lean_ctor_set_usize(v_reuseFailAlloc_723_, 4, v_shift_697_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v___x_729_; 
lean_del_object(v___x_710_);
v___x_725_ = lean_array_fget(v_snd_707_, v___x_699_);
lean_dec(v_snd_707_);
v___x_726_ = ((size_t)5ULL);
v___x_727_ = lean_usize_sub(v_shift_697_, v___x_726_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 3, v_newTailOff_716_);
lean_ctor_set(v___x_705_, 2, v_newSize_714_);
lean_ctor_set(v___x_705_, 1, v_last_712_);
lean_ctor_set(v___x_705_, 0, v___x_725_);
v___x_729_ = v___x_705_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_last_712_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_newSize_714_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_newTailOff_716_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_ctor_set_usize(v___x_729_, 4, v___x_727_);
return v___x_729_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_tailOff_698_);
lean_inc(v_size_696_);
lean_inc_ref(v_tail_695_);
lean_inc_ref(v_root_694_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_t_693_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_751_ = lean_ctor_get(v_t_693_, 3);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_t_693_, 2);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_t_693_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_t_693_, 0);
lean_dec(v_unused_754_);
v___x_742_ = v_t_693_;
v_isShared_743_ = v_isSharedCheck_750_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_t_693_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_750_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_744_ = lean_array_pop(v_tail_695_);
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_sub(v_size_696_, v___x_745_);
lean_dec(v_size_696_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 2, v___x_746_);
lean_ctor_set(v___x_742_, 1, v___x_744_);
v___x_748_ = v___x_742_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_root_694_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_tailOff_698_);
lean_ctor_set_usize(v_reuseFailAlloc_749_, 4, v_shift_697_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_755_, lean_object* v_t_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PersistentArray_pop___redArg(v_t_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_758_, lean_object* v_f_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_toApplicative_762_; lean_object* v_cs_763_; lean_object* v_toPure_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_toApplicative_762_ = lean_ctor_get(v_inst_758_, 0);
v_cs_763_ = lean_ctor_get(v_x_760_, 0);
lean_inc_ref(v_cs_763_);
lean_dec_ref_known(v_x_760_, 1);
v_toPure_764_ = lean_ctor_get(v_toApplicative_762_, 1);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_array_get_size(v_cs_763_);
v___x_767_ = lean_nat_dec_lt(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_inc(v_toPure_764_);
lean_dec_ref(v_cs_763_);
lean_dec(v_f_759_);
lean_dec_ref(v_inst_758_);
v___x_768_ = lean_apply_2(v_toPure_764_, lean_box(0), v_x_761_);
return v___x_768_;
}
else
{
lean_object* v___f_769_; uint8_t v___x_770_; 
lean_inc_ref(v_inst_758_);
v___f_769_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_769_, 0, v_inst_758_);
lean_closure_set(v___f_769_, 1, v_f_759_);
v___x_770_ = lean_nat_dec_le(v___x_766_, v___x_766_);
if (v___x_770_ == 0)
{
if (v___x_767_ == 0)
{
lean_object* v___x_771_; 
lean_inc(v_toPure_764_);
lean_dec_ref(v___f_769_);
lean_dec_ref(v_cs_763_);
lean_dec_ref(v_inst_758_);
v___x_771_ = lean_apply_2(v_toPure_764_, lean_box(0), v_x_761_);
return v___x_771_;
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_766_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_758_, v___f_769_, v_cs_763_, v___x_772_, v___x_773_, v_x_761_);
return v___x_774_;
}
}
else
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_766_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_758_, v___f_769_, v_cs_763_, v___x_775_, v___x_776_, v_x_761_);
return v___x_777_;
}
}
}
else
{
lean_object* v_toApplicative_778_; lean_object* v_vs_779_; lean_object* v_toPure_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_toApplicative_778_ = lean_ctor_get(v_inst_758_, 0);
v_vs_779_ = lean_ctor_get(v_x_760_, 0);
lean_inc_ref(v_vs_779_);
lean_dec_ref_known(v_x_760_, 1);
v_toPure_780_ = lean_ctor_get(v_toApplicative_778_, 1);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v_vs_779_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_inc(v_toPure_780_);
lean_dec_ref(v_vs_779_);
lean_dec(v_f_759_);
lean_dec_ref(v_inst_758_);
v___x_784_ = lean_apply_2(v_toPure_780_, lean_box(0), v_x_761_);
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_785_ == 0)
{
if (v___x_783_ == 0)
{
lean_object* v___x_786_; 
lean_inc(v_toPure_780_);
lean_dec_ref(v_vs_779_);
lean_dec(v_f_759_);
lean_dec_ref(v_inst_758_);
v___x_786_ = lean_apply_2(v_toPure_780_, lean_box(0), v_x_761_);
return v___x_786_;
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_of_nat(v___x_782_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_758_, v_f_759_, v_vs_779_, v___x_787_, v___x_788_, v_x_761_);
return v___x_789_;
}
}
else
{
size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_782_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_758_, v_f_759_, v_vs_779_, v___x_790_, v___x_791_, v_x_761_);
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_793_, lean_object* v_f_794_, lean_object* v_b_795_, lean_object* v_c_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_793_, v_f_794_, v_c_796_, v_b_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_798_, lean_object* v_m_799_, lean_object* v_inst_800_, lean_object* v_00_u03b2_801_, lean_object* v_f_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_800_, v_f_802_, v_x_803_, v_x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_toApplicative_806_, lean_object* v_j_807_, lean_object* v_cs_808_, lean_object* v_inst_809_, lean_object* v___f_810_, lean_object* v_b_811_){
_start:
{
lean_object* v_toPure_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_toPure_812_ = lean_ctor_get(v_toApplicative_806_, 1);
lean_inc(v_toPure_812_);
lean_dec_ref(v_toApplicative_806_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_j_807_, v___x_813_);
v___x_815_ = lean_array_get_size(v_cs_808_);
v___x_816_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v___x_814_);
lean_dec(v___f_810_);
lean_dec_ref(v_inst_809_);
lean_dec_ref(v_cs_808_);
v___x_817_ = lean_apply_2(v_toPure_812_, lean_box(0), v_b_811_);
return v___x_817_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_le(v___x_815_, v___x_815_);
if (v___x_818_ == 0)
{
if (v___x_816_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v___x_814_);
lean_dec(v___f_810_);
lean_dec_ref(v_inst_809_);
lean_dec_ref(v_cs_808_);
v___x_819_ = lean_apply_2(v_toPure_812_, lean_box(0), v_b_811_);
return v___x_819_;
}
else
{
size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
lean_dec(v_toPure_812_);
v___x_820_ = lean_usize_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___x_821_ = lean_usize_of_nat(v___x_815_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_809_, v___f_810_, v_cs_808_, v___x_820_, v___x_821_, v_b_811_);
return v___x_822_;
}
}
else
{
size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; 
lean_dec(v_toPure_812_);
v___x_823_ = lean_usize_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___x_824_ = lean_usize_of_nat(v___x_815_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_809_, v___f_810_, v_cs_808_, v___x_823_, v___x_824_, v_b_811_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_826_, lean_object* v_j_827_, lean_object* v_cs_828_, lean_object* v_inst_829_, lean_object* v___f_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_toApplicative_826_, v_j_827_, v_cs_828_, v_inst_829_, v___f_830_, v_b_831_);
lean_dec(v_j_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_833_, lean_object* v_f_834_, lean_object* v_x_835_, size_t v_x_836_, size_t v_x_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v_toApplicative_839_; lean_object* v_toBind_840_; lean_object* v_cs_841_; lean_object* v___f_842_; lean_object* v___x_843_; size_t v___x_844_; lean_object* v_j_845_; lean_object* v___f_846_; lean_object* v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_toApplicative_839_ = lean_ctor_get(v_inst_833_, 0);
v_toBind_840_ = lean_ctor_get(v_inst_833_, 1);
lean_inc(v_toBind_840_);
v_cs_841_ = lean_ctor_get(v_x_835_, 0);
lean_inc_ref_n(v_cs_841_, 2);
lean_dec_ref_known(v_x_835_, 1);
lean_inc(v_f_834_);
lean_inc_ref_n(v_inst_833_, 2);
v___f_842_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_842_, 0, v_inst_833_);
lean_closure_set(v___f_842_, 1, v_f_834_);
v___x_843_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_844_ = lean_usize_shift_right(v_x_836_, v_x_837_);
v_j_845_ = lean_usize_to_nat(v___x_844_);
lean_inc(v_j_845_);
lean_inc_ref(v_toApplicative_839_);
v___f_846_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_846_, 0, v_toApplicative_839_);
lean_closure_set(v___f_846_, 1, v_j_845_);
lean_closure_set(v___f_846_, 2, v_cs_841_);
lean_closure_set(v___f_846_, 3, v_inst_833_);
lean_closure_set(v___f_846_, 4, v___f_842_);
v___x_847_ = lean_array_get(v___x_843_, v_cs_841_, v_j_845_);
lean_dec(v_j_845_);
lean_dec_ref(v_cs_841_);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_shift_left(v___x_848_, v_x_837_);
v___x_850_ = lean_usize_sub(v___x_849_, v___x_848_);
v___x_851_ = lean_usize_land(v_x_836_, v___x_850_);
v___x_852_ = ((size_t)5ULL);
v___x_853_ = lean_usize_sub(v_x_837_, v___x_852_);
v___x_854_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_833_, v_f_834_, v___x_847_, v___x_851_, v___x_853_, v_x_838_);
v___x_855_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v___x_854_, v___f_846_);
return v___x_855_;
}
else
{
lean_object* v_toApplicative_856_; lean_object* v_vs_857_; lean_object* v_toPure_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_toApplicative_856_ = lean_ctor_get(v_inst_833_, 0);
v_vs_857_ = lean_ctor_get(v_x_835_, 0);
lean_inc_ref(v_vs_857_);
lean_dec_ref_known(v_x_835_, 1);
v_toPure_858_ = lean_ctor_get(v_toApplicative_856_, 1);
v___x_859_ = lean_usize_to_nat(v_x_836_);
v___x_860_ = lean_array_get_size(v_vs_857_);
v___x_861_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_inc(v_toPure_858_);
lean_dec(v___x_859_);
lean_dec_ref(v_vs_857_);
lean_dec(v_f_834_);
lean_dec_ref(v_inst_833_);
v___x_862_ = lean_apply_2(v_toPure_858_, lean_box(0), v_x_838_);
return v___x_862_;
}
else
{
uint8_t v___x_863_; 
v___x_863_ = lean_nat_dec_le(v___x_860_, v___x_860_);
if (v___x_863_ == 0)
{
if (v___x_861_ == 0)
{
lean_object* v___x_864_; 
lean_inc(v_toPure_858_);
lean_dec(v___x_859_);
lean_dec_ref(v_vs_857_);
lean_dec(v_f_834_);
lean_dec_ref(v_inst_833_);
v___x_864_ = lean_apply_2(v_toPure_858_, lean_box(0), v_x_838_);
return v___x_864_;
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_usize_of_nat(v___x_859_);
lean_dec(v___x_859_);
v___x_866_ = lean_usize_of_nat(v___x_860_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_833_, v_f_834_, v_vs_857_, v___x_865_, v___x_866_, v_x_838_);
return v___x_867_;
}
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_868_ = lean_usize_of_nat(v___x_859_);
lean_dec(v___x_859_);
v___x_869_ = lean_usize_of_nat(v___x_860_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_833_, v_f_834_, v_vs_857_, v___x_868_, v___x_869_, v_x_838_);
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_871_, lean_object* v_f_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
size_t v_x_207__boxed_877_; size_t v_x_208__boxed_878_; lean_object* v_res_879_; 
v_x_207__boxed_877_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_x_208__boxed_878_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_res_879_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_871_, v_f_872_, v_x_873_, v_x_207__boxed_877_, v_x_208__boxed_878_, v_x_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_880_, lean_object* v_m_881_, lean_object* v_inst_882_, lean_object* v_00_u03b2_883_, lean_object* v_f_884_, lean_object* v_x_885_, size_t v_x_886_, size_t v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_882_, v_f_884_, v_x_885_, v_x_886_, v_x_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_890_, lean_object* v_m_891_, lean_object* v_inst_892_, lean_object* v_00_u03b2_893_, lean_object* v_f_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
size_t v_x_276__boxed_899_; size_t v_x_277__boxed_900_; lean_object* v_res_901_; 
v_x_276__boxed_899_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_x_277__boxed_900_ = lean_unbox_usize(v_x_897_);
lean_dec(v_x_897_);
v_res_901_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_890_, v_m_891_, v_inst_892_, v_00_u03b2_893_, v_f_894_, v_x_895_, v_x_276__boxed_899_, v_x_277__boxed_900_, v_x_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_toApplicative_902_, lean_object* v_tail_903_, lean_object* v___x_904_, lean_object* v_inst_905_, lean_object* v_f_906_, lean_object* v_b_907_){
_start:
{
lean_object* v_toPure_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_toPure_908_ = lean_ctor_get(v_toApplicative_902_, 1);
lean_inc(v_toPure_908_);
lean_dec_ref(v_toApplicative_902_);
v___x_909_ = lean_array_get_size(v_tail_903_);
v___x_910_ = lean_nat_dec_lt(v___x_904_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec(v_f_906_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_tail_903_);
v___x_911_ = lean_apply_2(v_toPure_908_, lean_box(0), v_b_907_);
return v___x_911_;
}
else
{
uint8_t v___x_912_; 
v___x_912_ = lean_nat_dec_le(v___x_909_, v___x_909_);
if (v___x_912_ == 0)
{
if (v___x_910_ == 0)
{
lean_object* v___x_913_; 
lean_dec(v_f_906_);
lean_dec_ref(v_inst_905_);
lean_dec_ref(v_tail_903_);
v___x_913_ = lean_apply_2(v_toPure_908_, lean_box(0), v_b_907_);
return v___x_913_;
}
else
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
lean_dec(v_toPure_908_);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_909_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_905_, v_f_906_, v_tail_903_, v___x_914_, v___x_915_, v_b_907_);
return v___x_916_;
}
}
else
{
size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
lean_dec(v_toPure_908_);
v___x_917_ = ((size_t)0ULL);
v___x_918_ = lean_usize_of_nat(v___x_909_);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_905_, v_f_906_, v_tail_903_, v___x_917_, v___x_918_, v_b_907_);
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_toApplicative_920_, lean_object* v_tail_921_, lean_object* v___x_922_, lean_object* v_inst_923_, lean_object* v_f_924_, lean_object* v_b_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_toApplicative_920_, v_tail_921_, v___x_922_, v_inst_923_, v_f_924_, v_b_925_);
lean_dec(v___x_922_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_927_, lean_object* v_t_928_, lean_object* v_f_929_, lean_object* v_init_930_, lean_object* v_start_931_){
_start:
{
lean_object* v_toApplicative_932_; lean_object* v_toBind_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_toApplicative_932_ = lean_ctor_get(v_inst_927_, 0);
v_toBind_933_ = lean_ctor_get(v_inst_927_, 1);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_nat_dec_eq(v_start_931_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v_root_936_; lean_object* v_tail_937_; size_t v_shift_938_; lean_object* v_tailOff_939_; uint8_t v___x_940_; 
v_root_936_ = lean_ctor_get(v_t_928_, 0);
lean_inc_ref(v_root_936_);
v_tail_937_ = lean_ctor_get(v_t_928_, 1);
lean_inc_ref(v_tail_937_);
v_shift_938_ = lean_ctor_get_usize(v_t_928_, 4);
v_tailOff_939_ = lean_ctor_get(v_t_928_, 3);
lean_inc(v_tailOff_939_);
lean_dec_ref(v_t_928_);
v___x_940_ = lean_nat_dec_le(v_tailOff_939_, v_start_931_);
if (v___x_940_ == 0)
{
lean_object* v___f_941_; size_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_inc(v_toBind_933_);
lean_dec(v_tailOff_939_);
lean_inc(v_f_929_);
lean_inc_ref(v_inst_927_);
lean_inc_ref(v_toApplicative_932_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_941_, 0, v_toApplicative_932_);
lean_closure_set(v___f_941_, 1, v_tail_937_);
lean_closure_set(v___f_941_, 2, v___x_934_);
lean_closure_set(v___f_941_, 3, v_inst_927_);
lean_closure_set(v___f_941_, 4, v_f_929_);
v___x_942_ = lean_usize_of_nat(v_start_931_);
v___x_943_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_927_, v_f_929_, v_root_936_, v___x_942_, v_shift_938_, v_init_930_);
v___x_944_ = lean_apply_4(v_toBind_933_, lean_box(0), lean_box(0), v___x_943_, v___f_941_);
return v___x_944_;
}
else
{
lean_object* v_toPure_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
lean_dec_ref(v_root_936_);
v_toPure_945_ = lean_ctor_get(v_toApplicative_932_, 1);
v___x_946_ = lean_nat_sub(v_start_931_, v_tailOff_939_);
lean_dec(v_tailOff_939_);
v___x_947_ = lean_array_get_size(v_tail_937_);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_inc(v_toPure_945_);
lean_dec(v___x_946_);
lean_dec_ref(v_tail_937_);
lean_dec(v_f_929_);
lean_dec_ref(v_inst_927_);
v___x_949_ = lean_apply_2(v_toPure_945_, lean_box(0), v_init_930_);
return v___x_949_;
}
else
{
uint8_t v___x_950_; 
v___x_950_ = lean_nat_dec_le(v___x_947_, v___x_947_);
if (v___x_950_ == 0)
{
if (v___x_948_ == 0)
{
lean_object* v___x_951_; 
lean_inc(v_toPure_945_);
lean_dec(v___x_946_);
lean_dec_ref(v_tail_937_);
lean_dec(v_f_929_);
lean_dec_ref(v_inst_927_);
v___x_951_ = lean_apply_2(v_toPure_945_, lean_box(0), v_init_930_);
return v___x_951_;
}
else
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_usize_of_nat(v___x_946_);
lean_dec(v___x_946_);
v___x_953_ = lean_usize_of_nat(v___x_947_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_927_, v_f_929_, v_tail_937_, v___x_952_, v___x_953_, v_init_930_);
return v___x_954_;
}
}
else
{
size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_usize_of_nat(v___x_946_);
lean_dec(v___x_946_);
v___x_956_ = lean_usize_of_nat(v___x_947_);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_927_, v_f_929_, v_tail_937_, v___x_955_, v___x_956_, v_init_930_);
return v___x_957_;
}
}
}
}
else
{
lean_object* v_root_958_; lean_object* v_tail_959_; lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
lean_inc(v_toBind_933_);
v_root_958_ = lean_ctor_get(v_t_928_, 0);
lean_inc_ref(v_root_958_);
v_tail_959_ = lean_ctor_get(v_t_928_, 1);
lean_inc_ref(v_tail_959_);
lean_dec_ref(v_t_928_);
lean_inc(v_f_929_);
lean_inc_ref(v_inst_927_);
lean_inc_ref(v_toApplicative_932_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_960_, 0, v_toApplicative_932_);
lean_closure_set(v___f_960_, 1, v_tail_959_);
lean_closure_set(v___f_960_, 2, v___x_934_);
lean_closure_set(v___f_960_, 3, v_inst_927_);
lean_closure_set(v___f_960_, 4, v_f_929_);
v___x_961_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_927_, v_f_929_, v_root_958_, v_init_930_);
v___x_962_ = lean_apply_4(v_toBind_933_, lean_box(0), lean_box(0), v___x_961_, v___f_960_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_963_, lean_object* v_t_964_, lean_object* v_f_965_, lean_object* v_init_966_, lean_object* v_start_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_963_, v_t_964_, v_f_965_, v_init_966_, v_start_967_);
lean_dec(v_start_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_969_, lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_00_u03b2_972_, lean_object* v_t_973_, lean_object* v_f_974_, lean_object* v_init_975_, lean_object* v_start_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_971_, v_t_973_, v_f_974_, v_init_975_, v_start_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_978_, lean_object* v_m_979_, lean_object* v_inst_980_, lean_object* v_00_u03b2_981_, lean_object* v_t_982_, lean_object* v_f_983_, lean_object* v_init_984_, lean_object* v_start_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_978_, v_m_979_, v_inst_980_, v_00_u03b2_981_, v_t_982_, v_f_983_, v_init_984_, v_start_985_);
lean_dec(v_start_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
if (lean_obj_tag(v_x_989_) == 0)
{
lean_object* v_toApplicative_991_; lean_object* v_cs_992_; lean_object* v_toPure_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_toApplicative_991_ = lean_ctor_get(v_inst_987_, 0);
v_cs_992_ = lean_ctor_get(v_x_989_, 0);
lean_inc_ref(v_cs_992_);
lean_dec_ref_known(v_x_989_, 1);
v_toPure_993_ = lean_ctor_get(v_toApplicative_991_, 1);
v___x_994_ = lean_array_get_size(v_cs_992_);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_nat_dec_lt(v___x_995_, v___x_994_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_inc(v_toPure_993_);
lean_dec_ref(v_cs_992_);
lean_dec(v_f_988_);
lean_dec_ref(v_inst_987_);
v___x_997_ = lean_apply_2(v_toPure_993_, lean_box(0), v_x_990_);
return v___x_997_;
}
else
{
lean_object* v___f_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
lean_inc_ref(v_inst_987_);
v___f_998_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_998_, 0, v_inst_987_);
lean_closure_set(v___f_998_, 1, v_f_988_);
v___x_999_ = lean_usize_of_nat(v___x_994_);
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_987_, v___f_998_, v_cs_992_, v___x_999_, v___x_1000_, v_x_990_);
return v___x_1001_;
}
}
else
{
lean_object* v_toApplicative_1002_; lean_object* v_vs_1003_; lean_object* v_toPure_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_toApplicative_1002_ = lean_ctor_get(v_inst_987_, 0);
v_vs_1003_ = lean_ctor_get(v_x_989_, 0);
lean_inc_ref(v_vs_1003_);
lean_dec_ref_known(v_x_989_, 1);
v_toPure_1004_ = lean_ctor_get(v_toApplicative_1002_, 1);
v___x_1005_ = lean_array_get_size(v_vs_1003_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_lt(v___x_1006_, v___x_1005_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_inc(v_toPure_1004_);
lean_dec_ref(v_vs_1003_);
lean_dec(v_f_988_);
lean_dec_ref(v_inst_987_);
v___x_1008_ = lean_apply_2(v_toPure_1004_, lean_box(0), v_x_990_);
return v___x_1008_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_usize_of_nat(v___x_1005_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_987_, v_f_988_, v_vs_1003_, v___x_1009_, v___x_1010_, v_x_990_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_1012_, lean_object* v_f_1013_, lean_object* v_c_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1012_, v_f_1013_, v_c_1014_, v_b_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_1017_, lean_object* v_m_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_inst_1020_, lean_object* v_f_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1020_, v_f_1021_, v_x_1022_, v_x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_1025_, lean_object* v_f_1026_, lean_object* v_root_1027_, lean_object* v_____do__lift_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1025_, v_f_1026_, v_root_1027_, v_____do__lift_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1030_, lean_object* v_t_1031_, lean_object* v_f_1032_, lean_object* v_init_1033_){
_start:
{
lean_object* v_toApplicative_1034_; lean_object* v_toBind_1035_; lean_object* v_root_1036_; lean_object* v_tail_1037_; lean_object* v_toPure_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_toApplicative_1034_ = lean_ctor_get(v_inst_1030_, 0);
v_toBind_1035_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc(v_toBind_1035_);
v_root_1036_ = lean_ctor_get(v_t_1031_, 0);
lean_inc_ref(v_root_1036_);
v_tail_1037_ = lean_ctor_get(v_t_1031_, 1);
lean_inc_ref(v_tail_1037_);
lean_dec_ref(v_t_1031_);
v_toPure_1038_ = lean_ctor_get(v_toApplicative_1034_, 1);
lean_inc(v_f_1032_);
lean_inc_ref(v_inst_1030_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1039_, 0, v_inst_1030_);
lean_closure_set(v___f_1039_, 1, v_f_1032_);
lean_closure_set(v___f_1039_, 2, v_root_1036_);
v___x_1040_ = lean_array_get_size(v_tail_1037_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_nat_dec_lt(v___x_1041_, v___x_1040_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_inc(v_toPure_1038_);
lean_dec_ref(v_tail_1037_);
lean_dec(v_f_1032_);
lean_dec_ref(v_inst_1030_);
v___x_1043_ = lean_apply_2(v_toPure_1038_, lean_box(0), v_init_1033_);
v___x_1044_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1043_, v___f_1039_);
return v___x_1044_;
}
else
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_usize_of_nat(v___x_1040_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1030_, v_f_1032_, v_tail_1037_, v___x_1045_, v___x_1046_, v_init_1033_);
v___x_1048_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1047_, v___f_1039_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1049_, lean_object* v_m_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_, lean_object* v_t_1053_, lean_object* v_f_1054_, lean_object* v_init_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1052_, v_t_1053_, v_f_1054_, v_init_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1057_, lean_object* v_____s_1058_){
_start:
{
lean_object* v_fst_1059_; 
v_fst_1059_ = lean_ctor_get(v_____s_1058_, 0);
if (lean_obj_tag(v_fst_1059_) == 0)
{
lean_object* v_snd_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_snd_1060_ = lean_ctor_get(v_____s_1058_, 1);
lean_inc(v_snd_1060_);
lean_dec_ref(v_____s_1058_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_snd_1060_);
v___x_1062_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1061_);
return v___x_1062_;
}
else
{
lean_object* v_val_1063_; lean_object* v___x_1064_; 
lean_inc_ref(v_fst_1059_);
lean_dec_ref(v_____s_1058_);
v_val_1063_ = lean_ctor_get(v_fst_1059_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v_fst_1059_, 1);
v___x_1064_ = lean_apply_2(v_toPure_1057_, lean_box(0), v_val_1063_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1065_, lean_object* v_toPure_1066_, lean_object* v___x_1067_, lean_object* v_____do__lift_1068_){
_start:
{
if (lean_obj_tag(v_____do__lift_1068_) == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_____do__lift_1068_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_snd_1065_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = lean_apply_2(v_toPure_1066_, lean_box(0), v___x_1071_);
return v___x_1072_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_snd_1065_);
v_a_1073_ = lean_ctor_get(v_____do__lift_1068_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_____do__lift_1068_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1075_ = v_____do__lift_1068_;
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v_____do__lift_1068_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1067_);
lean_ctor_set(v___x_1077_, 1, v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_apply_2(v_toPure_1066_, lean_box(0), v___x_1079_);
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1083_, lean_object* v___x_1084_, lean_object* v_f_1085_, lean_object* v_toBind_1086_, lean_object* v_a_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_snd_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_snd_1090_ = lean_ctor_get(v___y_1089_, 1);
lean_inc_n(v_snd_1090_, 2);
lean_dec_ref(v___y_1089_);
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1091_, 0, v_snd_1090_);
lean_closure_set(v___f_1091_, 1, v_toPure_1083_);
lean_closure_set(v___f_1091_, 2, v___x_1084_);
v___x_1092_ = lean_apply_2(v_f_1085_, v_a_1087_, v_snd_1090_);
v___x_1093_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v___x_1092_, v___f_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1094_, lean_object* v___x_1095_, lean_object* v_inst_1096_, lean_object* v_f_1097_, lean_object* v_toBind_1098_, lean_object* v_a_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1094_, v___x_1095_, v_inst_1096_, v_f_1097_, v_toBind_1098_, v_a_1099_, v_x_1100_, v___y_1101_);
lean_dec_ref(v_a_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1103_, lean_object* v_f_1104_, lean_object* v_n_1105_, lean_object* v_b_1106_){
_start:
{
if (lean_obj_tag(v_n_1105_) == 0)
{
lean_object* v_toApplicative_1107_; lean_object* v_toBind_1108_; lean_object* v_toPure_1109_; lean_object* v_cs_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_toApplicative_1107_ = lean_ctor_get(v_inst_1103_, 0);
v_toBind_1108_ = lean_ctor_get(v_inst_1103_, 1);
lean_inc_n(v_toBind_1108_, 2);
v_toPure_1109_ = lean_ctor_get(v_toApplicative_1107_, 1);
v_cs_1110_ = lean_ctor_get(v_n_1105_, 0);
lean_inc_n(v_toPure_1109_, 2);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1111_, 0, v_toPure_1109_);
v___x_1112_ = lean_box(0);
lean_inc_ref(v_inst_1103_);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1113_, 0, v_toPure_1109_);
lean_closure_set(v___f_1113_, 1, v___x_1112_);
lean_closure_set(v___f_1113_, 2, v_inst_1103_);
lean_closure_set(v___f_1113_, 3, v_f_1104_);
lean_closure_set(v___f_1113_, 4, v_toBind_1108_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v_b_1106_);
v_sz_1115_ = lean_array_size(v_cs_1110_);
v___x_1116_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1110_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1103_, v_cs_1110_, v___f_1113_, v_sz_1115_, v___x_1116_, v___x_1114_);
v___x_1118_ = lean_apply_4(v_toBind_1108_, lean_box(0), lean_box(0), v___x_1117_, v___f_1111_);
return v___x_1118_;
}
else
{
lean_object* v_toApplicative_1119_; lean_object* v_toBind_1120_; lean_object* v_toPure_1121_; lean_object* v_vs_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; size_t v_sz_1127_; size_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_toApplicative_1119_ = lean_ctor_get(v_inst_1103_, 0);
v_toBind_1120_ = lean_ctor_get(v_inst_1103_, 1);
lean_inc_n(v_toBind_1120_, 2);
v_toPure_1121_ = lean_ctor_get(v_toApplicative_1119_, 1);
v_vs_1122_ = lean_ctor_get(v_n_1105_, 0);
lean_inc_n(v_toPure_1121_, 2);
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1123_, 0, v_toPure_1121_);
v___x_1124_ = lean_box(0);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1125_, 0, v_toPure_1121_);
lean_closure_set(v___f_1125_, 1, v___x_1124_);
lean_closure_set(v___f_1125_, 2, v_f_1104_);
lean_closure_set(v___f_1125_, 3, v_toBind_1120_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v_b_1106_);
v_sz_1127_ = lean_array_size(v_vs_1122_);
v___x_1128_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1122_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1103_, v_vs_1122_, v___f_1125_, v_sz_1127_, v___x_1128_, v___x_1126_);
v___x_1130_ = lean_apply_4(v_toBind_1120_, lean_box(0), lean_box(0), v___x_1129_, v___f_1123_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1131_, lean_object* v___x_1132_, lean_object* v_inst_1133_, lean_object* v_f_1134_, lean_object* v_toBind_1135_, lean_object* v_a_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_snd_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_snd_1139_ = lean_ctor_get(v___y_1138_, 1);
lean_inc_n(v_snd_1139_, 2);
lean_dec_ref(v___y_1138_);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1140_, 0, v_snd_1139_);
lean_closure_set(v___f_1140_, 1, v_toPure_1131_);
lean_closure_set(v___f_1140_, 2, v___x_1132_);
v___x_1141_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1133_, v_f_1134_, v_a_1136_, v_snd_1139_);
v___x_1142_ = lean_apply_4(v_toBind_1135_, lean_box(0), lean_box(0), v___x_1141_, v___f_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1143_, lean_object* v_f_1144_, lean_object* v_n_1145_, lean_object* v_b_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1143_, v_f_1144_, v_n_1145_, v_b_1146_);
lean_dec_ref(v_n_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_m_1150_, lean_object* v_inst_1151_, lean_object* v_inh_1152_, lean_object* v_f_1153_, lean_object* v_n_1154_, lean_object* v_b_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1151_, v_f_1153_, v_n_1154_, v_b_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_inh_1161_, lean_object* v_f_1162_, lean_object* v_n_1163_, lean_object* v_b_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1157_, v_00_u03b2_1158_, v_m_1159_, v_inst_1160_, v_inh_1161_, v_f_1162_, v_n_1163_, v_b_1164_);
lean_dec_ref(v_n_1163_);
lean_dec(v_inh_1161_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1166_, lean_object* v_____s_1167_){
_start:
{
lean_object* v_fst_1168_; 
v_fst_1168_ = lean_ctor_get(v_____s_1167_, 0);
if (lean_obj_tag(v_fst_1168_) == 0)
{
lean_object* v_snd_1169_; lean_object* v___x_1170_; 
v_snd_1169_ = lean_ctor_get(v_____s_1167_, 1);
lean_inc(v_snd_1169_);
lean_dec_ref(v_____s_1167_);
v___x_1170_ = lean_apply_2(v_toPure_1166_, lean_box(0), v_snd_1169_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; lean_object* v___x_1172_; 
lean_inc_ref(v_fst_1168_);
lean_dec_ref(v_____s_1167_);
v_val_1171_ = lean_ctor_get(v_fst_1168_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v_fst_1168_, 1);
v___x_1172_ = lean_apply_2(v_toPure_1166_, lean_box(0), v_val_1171_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1173_, lean_object* v_toPure_1174_, lean_object* v___x_1175_, lean_object* v_____do__lift_1176_){
_start:
{
if (lean_obj_tag(v_____do__lift_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v___x_1175_);
v_a_1177_ = lean_ctor_get(v_____do__lift_1176_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_____do__lift_1176_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1179_ = v_____do__lift_1176_;
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v_____do__lift_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1187_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1177_);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v_snd_1173_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_apply_2(v_toPure_1174_, lean_box(0), v___x_1184_);
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_snd_1173_);
v_a_1188_ = lean_ctor_get(v_____do__lift_1176_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_____do__lift_1176_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1190_ = v_____do__lift_1176_;
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v_____do__lift_1176_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1175_);
lean_ctor_set(v___x_1192_, 1, v_a_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_apply_2(v_toPure_1174_, lean_box(0), v___x_1194_);
return v___x_1195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1198_, lean_object* v___x_1199_, lean_object* v_f_1200_, lean_object* v_toBind_1201_, lean_object* v_a_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_snd_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_snd_1205_ = lean_ctor_get(v___y_1204_, 1);
lean_inc_n(v_snd_1205_, 2);
lean_dec_ref(v___y_1204_);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1206_, 0, v_snd_1205_);
lean_closure_set(v___f_1206_, 1, v_toPure_1198_);
lean_closure_set(v___f_1206_, 2, v___x_1199_);
v___x_1207_ = lean_apply_2(v_f_1200_, v_a_1202_, v_snd_1205_);
v___x_1208_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v___x_1207_, v___f_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1209_, lean_object* v_f_1210_, lean_object* v_toBind_1211_, lean_object* v_tail_1212_, lean_object* v_inst_1213_, lean_object* v___f_1214_, lean_object* v_____do__lift_1215_){
_start:
{
if (lean_obj_tag(v_____do__lift_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
lean_dec(v___f_1214_);
lean_dec_ref(v_inst_1213_);
lean_dec_ref(v_tail_1212_);
lean_dec(v_toBind_1211_);
lean_dec(v_f_1210_);
v_a_1216_ = lean_ctor_get(v_____do__lift_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v_____do__lift_1215_, 1);
v___x_1217_ = lean_apply_2(v_toPure_1209_, lean_box(0), v_a_1216_);
return v___x_1217_;
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; size_t v_sz_1222_; size_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_a_1218_ = lean_ctor_get(v_____do__lift_1215_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v_____do__lift_1215_, 1);
v___x_1219_ = lean_box(0);
lean_inc(v_toBind_1211_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1220_, 0, v_toPure_1209_);
lean_closure_set(v___f_1220_, 1, v___x_1219_);
lean_closure_set(v___f_1220_, 2, v_f_1210_);
lean_closure_set(v___f_1220_, 3, v_toBind_1211_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v_a_1218_);
v_sz_1222_ = lean_array_size(v_tail_1212_);
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1213_, v_tail_1212_, v___f_1220_, v_sz_1222_, v___x_1223_, v___x_1221_);
v___x_1225_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1224_, v___f_1214_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1226_, lean_object* v_t_1227_, lean_object* v_init_1228_, lean_object* v_f_1229_){
_start:
{
lean_object* v_toApplicative_1230_; lean_object* v_toBind_1231_; lean_object* v_root_1232_; lean_object* v_tail_1233_; lean_object* v_toPure_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; 
v_toApplicative_1230_ = lean_ctor_get(v_inst_1226_, 0);
v_toBind_1231_ = lean_ctor_get(v_inst_1226_, 1);
lean_inc_n(v_toBind_1231_, 2);
v_root_1232_ = lean_ctor_get(v_t_1227_, 0);
v_tail_1233_ = lean_ctor_get(v_t_1227_, 1);
v_toPure_1234_ = lean_ctor_get(v_toApplicative_1230_, 1);
lean_inc_n(v_toPure_1234_, 2);
lean_inc(v_f_1229_);
lean_inc_ref(v_inst_1226_);
v___x_1235_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1226_, v_f_1229_, v_root_1232_, v_init_1228_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1236_, 0, v_toPure_1234_);
lean_inc_ref(v_tail_1233_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1237_, 0, v_toPure_1234_);
lean_closure_set(v___f_1237_, 1, v_f_1229_);
lean_closure_set(v___f_1237_, 2, v_toBind_1231_);
lean_closure_set(v___f_1237_, 3, v_tail_1233_);
lean_closure_set(v___f_1237_, 4, v_inst_1226_);
lean_closure_set(v___f_1237_, 5, v___f_1236_);
v___x_1238_ = lean_apply_4(v_toBind_1231_, lean_box(0), lean_box(0), v___x_1235_, v___f_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1239_, lean_object* v_t_1240_, lean_object* v_init_1241_, lean_object* v_f_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1239_, v_t_1240_, v_init_1241_, v_f_1242_);
lean_dec_ref(v_t_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1244_, lean_object* v_m_1245_, lean_object* v_inst_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_t_1248_, lean_object* v_init_1249_, lean_object* v_f_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1246_, v_t_1248_, v_init_1249_, v_f_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_m_1253_, lean_object* v_inst_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_t_1256_, lean_object* v_init_1257_, lean_object* v_f_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1252_, v_m_1253_, v_inst_1254_, v_00_u03b2_1255_, v_t_1256_, v_init_1257_, v_f_1258_);
lean_dec_ref(v_t_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1261_, 0, lean_box(0));
lean_closure_set(v___x_1261_, 1, lean_box(0));
lean_closure_set(v___x_1261_, 2, v_inst_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1262_, lean_object* v_m_1263_, lean_object* v_inst_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1265_, 0, lean_box(0));
lean_closure_set(v___x_1265_, 1, lean_box(0));
lean_closure_set(v___x_1265_, 2, v_inst_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1266_, lean_object* v_____s_1267_){
_start:
{
lean_object* v_fst_1268_; 
v_fst_1268_ = lean_ctor_get(v_____s_1267_, 0);
lean_inc(v_fst_1268_);
lean_dec_ref(v_____s_1267_);
if (lean_obj_tag(v_fst_1268_) == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_apply_2(v_toPure_1266_, lean_box(0), v___x_1269_);
return v___x_1270_;
}
else
{
lean_object* v_val_1271_; lean_object* v___x_1272_; 
v_val_1271_ = lean_ctor_get(v_fst_1268_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_fst_1268_, 1);
v___x_1272_ = lean_apply_2(v_toPure_1266_, lean_box(0), v_val_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1273_, lean_object* v_toPure_1274_, lean_object* v___x_1275_, lean_object* v_____do__lift_1276_){
_start:
{
if (lean_obj_tag(v_____do__lift_1276_) == 1)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_____do__lift_1276_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1273_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
v___x_1280_ = lean_apply_2(v_toPure_1274_, lean_box(0), v___x_1279_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v_____do__lift_1276_);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1275_);
v___x_1282_ = lean_apply_2(v_toPure_1274_, lean_box(0), v___x_1281_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1283_, lean_object* v_toBind_1284_, lean_object* v___f_1285_, lean_object* v_a_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_apply_1(v_f_1283_, v_a_1286_);
v___x_1290_ = lean_apply_4(v_toBind_1284_, lean_box(0), lean_box(0), v___x_1289_, v___f_1285_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1291_, lean_object* v_toBind_1292_, lean_object* v___f_1293_, lean_object* v_a_1294_, lean_object* v_x_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1291_, v_toBind_1292_, v___f_1293_, v_a_1294_, v_x_1295_, v___y_1296_);
lean_dec_ref(v___y_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1301_, lean_object* v_f_1302_, lean_object* v_toBind_1303_, lean_object* v___f_1304_, lean_object* v_a_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1301_, v_f_1302_, v_toBind_1303_, v___f_1304_, v_a_1305_, v_x_1306_, v___y_1307_);
lean_dec_ref(v___y_1307_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1309_, lean_object* v_f_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v_toApplicative_1312_; lean_object* v_cs_1313_; lean_object* v_toBind_1314_; lean_object* v_toPure_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_toApplicative_1312_ = lean_ctor_get(v_inst_1309_, 0);
v_cs_1313_ = lean_ctor_get(v_x_1311_, 0);
lean_inc_ref(v_cs_1313_);
lean_dec_ref_known(v_x_1311_, 1);
v_toBind_1314_ = lean_ctor_get(v_inst_1309_, 1);
lean_inc_n(v_toBind_1314_, 2);
v_toPure_1315_ = lean_ctor_get(v_toApplicative_1312_, 1);
v___x_1316_ = lean_box(0);
v___x_1317_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1315_, 2);
v___f_1318_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1318_, 0, v_toPure_1315_);
v___f_1319_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1319_, 0, v___x_1316_);
lean_closure_set(v___f_1319_, 1, v_toPure_1315_);
lean_closure_set(v___f_1319_, 2, v___x_1317_);
lean_inc_ref(v_inst_1309_);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1320_, 0, v_inst_1309_);
lean_closure_set(v___f_1320_, 1, v_f_1310_);
lean_closure_set(v___f_1320_, 2, v_toBind_1314_);
lean_closure_set(v___f_1320_, 3, v___f_1319_);
v_sz_1321_ = lean_array_size(v_cs_1313_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1309_, v_cs_1313_, v___f_1320_, v_sz_1321_, v___x_1322_, v___x_1317_);
v___x_1324_ = lean_apply_4(v_toBind_1314_, lean_box(0), lean_box(0), v___x_1323_, v___f_1318_);
return v___x_1324_;
}
else
{
lean_object* v_toApplicative_1325_; lean_object* v_vs_1326_; lean_object* v_toBind_1327_; lean_object* v_toPure_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; size_t v_sz_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_toApplicative_1325_ = lean_ctor_get(v_inst_1309_, 0);
v_vs_1326_ = lean_ctor_get(v_x_1311_, 0);
lean_inc_ref(v_vs_1326_);
lean_dec_ref_known(v_x_1311_, 1);
v_toBind_1327_ = lean_ctor_get(v_inst_1309_, 1);
lean_inc_n(v_toBind_1327_, 2);
v_toPure_1328_ = lean_ctor_get(v_toApplicative_1325_, 1);
v___x_1329_ = lean_box(0);
v___x_1330_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1328_, 2);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1331_, 0, v_toPure_1328_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1332_, 0, v___x_1329_);
lean_closure_set(v___f_1332_, 1, v_toPure_1328_);
lean_closure_set(v___f_1332_, 2, v___x_1330_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1333_, 0, v_f_1310_);
lean_closure_set(v___f_1333_, 1, v_toBind_1327_);
lean_closure_set(v___f_1333_, 2, v___f_1332_);
v_sz_1334_ = lean_array_size(v_vs_1326_);
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1309_, v_vs_1326_, v___f_1333_, v_sz_1334_, v___x_1335_, v___x_1330_);
v___x_1337_ = lean_apply_4(v_toBind_1327_, lean_box(0), lean_box(0), v___x_1336_, v___f_1331_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1338_, lean_object* v_f_1339_, lean_object* v_toBind_1340_, lean_object* v___f_1341_, lean_object* v_a_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1338_, v_f_1339_, v_a_1342_);
v___x_1346_ = lean_apply_4(v_toBind_1340_, lean_box(0), lean_box(0), v___x_1345_, v___f_1341_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1347_, lean_object* v_m_1348_, lean_object* v_inst_1349_, lean_object* v_00_u03b2_1350_, lean_object* v_f_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1349_, v_f_1351_, v_x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1354_, lean_object* v_____do__lift_1355_, lean_object* v_____s_1356_){
_start:
{
lean_object* v_fst_1357_; 
v_fst_1357_ = lean_ctor_get(v_____s_1356_, 0);
lean_inc(v_fst_1357_);
lean_dec_ref(v_____s_1356_);
if (lean_obj_tag(v_fst_1357_) == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_apply_2(v_toPure_1354_, lean_box(0), v_____do__lift_1355_);
return v___x_1358_;
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1360_; 
lean_dec(v_____do__lift_1355_);
v_val_1359_ = lean_ctor_get(v_fst_1357_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v_fst_1357_, 1);
v___x_1360_ = lean_apply_2(v_toPure_1354_, lean_box(0), v_val_1359_);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1361_, lean_object* v_toPure_1362_, lean_object* v___x_1363_, lean_object* v_____do__lift_1364_){
_start:
{
if (lean_obj_tag(v_____do__lift_1364_) == 1)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v___x_1363_);
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_____do__lift_1364_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1361_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
v___x_1368_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v_____do__lift_1364_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1363_);
v___x_1370_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1369_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1371_, lean_object* v_toBind_1372_, lean_object* v___f_1373_, lean_object* v_a_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_apply_1(v_f_1371_, v_a_1374_);
v___x_1378_ = lean_apply_4(v_toBind_1372_, lean_box(0), lean_box(0), v___x_1377_, v___f_1373_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1379_, lean_object* v_toBind_1380_, lean_object* v___f_1381_, lean_object* v_a_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1379_, v_toBind_1380_, v___f_1381_, v_a_1382_, v_x_1383_, v___y_1384_);
lean_dec_ref(v___y_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1386_, lean_object* v_f_1387_, lean_object* v_toBind_1388_, lean_object* v_tail_1389_, lean_object* v_inst_1390_, lean_object* v_____do__lift_1391_){
_start:
{
if (lean_obj_tag(v_____do__lift_1391_) == 0)
{
lean_object* v___f_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_inc(v_toPure_1386_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1392_, 0, v_toPure_1386_);
lean_closure_set(v___f_1392_, 1, v_____do__lift_1391_);
v___x_1393_ = lean_box(0);
v___x_1394_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1395_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1395_, 0, v___x_1393_);
lean_closure_set(v___f_1395_, 1, v_toPure_1386_);
lean_closure_set(v___f_1395_, 2, v___x_1394_);
lean_inc(v_toBind_1388_);
v___f_1396_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1396_, 0, v_f_1387_);
lean_closure_set(v___f_1396_, 1, v_toBind_1388_);
lean_closure_set(v___f_1396_, 2, v___f_1395_);
v_sz_1397_ = lean_array_size(v_tail_1389_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1390_, v_tail_1389_, v___f_1396_, v_sz_1397_, v___x_1398_, v___x_1394_);
v___x_1400_ = lean_apply_4(v_toBind_1388_, lean_box(0), lean_box(0), v___x_1399_, v___f_1392_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v_tail_1389_);
lean_dec(v_toBind_1388_);
lean_dec(v_f_1387_);
v___x_1401_ = lean_apply_2(v_toPure_1386_, lean_box(0), v_____do__lift_1391_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1402_, lean_object* v_t_1403_, lean_object* v_f_1404_){
_start:
{
lean_object* v_toApplicative_1405_; lean_object* v_toBind_1406_; lean_object* v_root_1407_; lean_object* v_tail_1408_; lean_object* v_toPure_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1402_, 0);
v_toBind_1406_ = lean_ctor_get(v_inst_1402_, 1);
lean_inc_n(v_toBind_1406_, 2);
v_root_1407_ = lean_ctor_get(v_t_1403_, 0);
lean_inc_ref(v_root_1407_);
v_tail_1408_ = lean_ctor_get(v_t_1403_, 1);
lean_inc_ref(v_tail_1408_);
lean_dec_ref(v_t_1403_);
v_toPure_1409_ = lean_ctor_get(v_toApplicative_1405_, 1);
lean_inc(v_toPure_1409_);
lean_inc(v_f_1404_);
lean_inc_ref(v_inst_1402_);
v___x_1410_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1402_, v_f_1404_, v_root_1407_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1411_, 0, v_toPure_1409_);
lean_closure_set(v___f_1411_, 1, v_f_1404_);
lean_closure_set(v___f_1411_, 2, v_toBind_1406_);
lean_closure_set(v___f_1411_, 3, v_tail_1408_);
lean_closure_set(v___f_1411_, 4, v_inst_1402_);
v___x_1412_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1410_, v___f_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1413_, lean_object* v_m_1414_, lean_object* v_inst_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_t_1417_, lean_object* v_f_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1415_, v_t_1417_, v_f_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1420_, lean_object* v_f_1421_, lean_object* v_x_1422_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_object* v_cs_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_cs_1423_ = lean_ctor_get(v_x_1422_, 0);
lean_inc_ref(v_cs_1423_);
lean_dec_ref_known(v_x_1422_, 1);
lean_inc_ref(v_inst_1420_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1424_, 0, v_inst_1420_);
lean_closure_set(v___f_1424_, 1, v_f_1421_);
v___x_1425_ = lean_array_get_size(v_cs_1423_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1420_, v___f_1424_, v_cs_1423_, v___x_1425_, lean_box(0));
return v___x_1426_;
}
else
{
lean_object* v_vs_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_vs_1427_ = lean_ctor_get(v_x_1422_, 0);
lean_inc_ref(v_vs_1427_);
lean_dec_ref_known(v_x_1422_, 1);
v___x_1428_ = lean_array_get_size(v_vs_1427_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1420_, v_f_1421_, v_vs_1427_, v___x_1428_, lean_box(0));
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1430_, lean_object* v_f_1431_, lean_object* v_c_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1430_, v_f_1431_, v_c_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1434_, lean_object* v_m_1435_, lean_object* v_inst_1436_, lean_object* v_00_u03b2_1437_, lean_object* v_f_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1436_, v_f_1438_, v_x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1441_, lean_object* v_f_1442_, lean_object* v_root_1443_, lean_object* v_toPure_1444_, lean_object* v_____do__lift_1445_){
_start:
{
if (lean_obj_tag(v_____do__lift_1445_) == 0)
{
lean_object* v___x_1446_; 
lean_dec(v_toPure_1444_);
v___x_1446_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1441_, v_f_1442_, v_root_1443_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v_root_1443_);
lean_dec(v_f_1442_);
lean_dec_ref(v_inst_1441_);
v___x_1447_ = lean_apply_2(v_toPure_1444_, lean_box(0), v_____do__lift_1445_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1448_, lean_object* v_t_1449_, lean_object* v_f_1450_){
_start:
{
lean_object* v_toApplicative_1451_; lean_object* v_toBind_1452_; lean_object* v_root_1453_; lean_object* v_tail_1454_; lean_object* v_toPure_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; 
v_toApplicative_1451_ = lean_ctor_get(v_inst_1448_, 0);
v_toBind_1452_ = lean_ctor_get(v_inst_1448_, 1);
lean_inc(v_toBind_1452_);
v_root_1453_ = lean_ctor_get(v_t_1449_, 0);
lean_inc_ref(v_root_1453_);
v_tail_1454_ = lean_ctor_get(v_t_1449_, 1);
lean_inc_ref(v_tail_1454_);
lean_dec_ref(v_t_1449_);
v_toPure_1455_ = lean_ctor_get(v_toApplicative_1451_, 1);
lean_inc(v_toPure_1455_);
v___x_1456_ = lean_array_get_size(v_tail_1454_);
lean_inc(v_f_1450_);
lean_inc_ref(v_inst_1448_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1448_, v_f_1450_, v_tail_1454_, v___x_1456_, lean_box(0));
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1458_, 0, v_inst_1448_);
lean_closure_set(v___f_1458_, 1, v_f_1450_);
lean_closure_set(v___f_1458_, 2, v_root_1453_);
lean_closure_set(v___f_1458_, 3, v_toPure_1455_);
v___x_1459_ = lean_apply_4(v_toBind_1452_, lean_box(0), lean_box(0), v___x_1457_, v___f_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1460_, lean_object* v_m_1461_, lean_object* v_inst_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_t_1464_, lean_object* v_f_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1462_, v_t_1464_, v_f_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_apply_1(v_f_1467_, v___y_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1471_, lean_object* v_f_1472_, lean_object* v_x_1473_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
lean_object* v_toApplicative_1474_; lean_object* v_cs_1475_; lean_object* v_toPure_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_toApplicative_1474_ = lean_ctor_get(v_inst_1471_, 0);
v_cs_1475_ = lean_ctor_get(v_x_1473_, 0);
lean_inc_ref(v_cs_1475_);
lean_dec_ref_known(v_x_1473_, 1);
v_toPure_1476_ = lean_ctor_get(v_toApplicative_1474_, 1);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_array_get_size(v_cs_1475_);
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_nat_dec_lt(v___x_1477_, v___x_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_inc(v_toPure_1476_);
lean_dec_ref(v_cs_1475_);
lean_dec(v_f_1472_);
lean_dec_ref(v_inst_1471_);
v___x_1481_ = lean_apply_2(v_toPure_1476_, lean_box(0), v___x_1479_);
return v___x_1481_;
}
else
{
lean_object* v___f_1482_; uint8_t v___x_1483_; 
lean_inc_ref(v_inst_1471_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1482_, 0, v_inst_1471_);
lean_closure_set(v___f_1482_, 1, v_f_1472_);
v___x_1483_ = lean_nat_dec_le(v___x_1478_, v___x_1478_);
if (v___x_1483_ == 0)
{
if (v___x_1480_ == 0)
{
lean_object* v___x_1484_; 
lean_inc(v_toPure_1476_);
lean_dec_ref(v___f_1482_);
lean_dec_ref(v_cs_1475_);
lean_dec_ref(v_inst_1471_);
v___x_1484_ = lean_apply_2(v_toPure_1476_, lean_box(0), v___x_1479_);
return v___x_1484_;
}
else
{
size_t v___x_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = lean_usize_of_nat(v___x_1478_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v___f_1482_, v_cs_1475_, v___x_1485_, v___x_1486_, v___x_1479_);
return v___x_1487_;
}
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1478_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v___f_1482_, v_cs_1475_, v___x_1488_, v___x_1489_, v___x_1479_);
return v___x_1490_;
}
}
}
else
{
lean_object* v_toApplicative_1491_; lean_object* v_vs_1492_; lean_object* v_toPure_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_toApplicative_1491_ = lean_ctor_get(v_inst_1471_, 0);
v_vs_1492_ = lean_ctor_get(v_x_1473_, 0);
lean_inc_ref(v_vs_1492_);
lean_dec_ref_known(v_x_1473_, 1);
v_toPure_1493_ = lean_ctor_get(v_toApplicative_1491_, 1);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_get_size(v_vs_1492_);
v___x_1496_ = lean_box(0);
v___x_1497_ = lean_nat_dec_lt(v___x_1494_, v___x_1495_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_inc(v_toPure_1493_);
lean_dec_ref(v_vs_1492_);
lean_dec(v_f_1472_);
lean_dec_ref(v_inst_1471_);
v___x_1498_ = lean_apply_2(v_toPure_1493_, lean_box(0), v___x_1496_);
return v___x_1498_;
}
else
{
lean_object* v___f_1499_; uint8_t v___x_1500_; 
v___f_1499_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1499_, 0, v_f_1472_);
v___x_1500_ = lean_nat_dec_le(v___x_1495_, v___x_1495_);
if (v___x_1500_ == 0)
{
if (v___x_1497_ == 0)
{
lean_object* v___x_1501_; 
lean_inc(v_toPure_1493_);
lean_dec_ref(v___f_1499_);
lean_dec_ref(v_vs_1492_);
lean_dec_ref(v_inst_1471_);
v___x_1501_ = lean_apply_2(v_toPure_1493_, lean_box(0), v___x_1496_);
return v___x_1501_;
}
else
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((size_t)0ULL);
v___x_1503_ = lean_usize_of_nat(v___x_1495_);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v___f_1499_, v_vs_1492_, v___x_1502_, v___x_1503_, v___x_1496_);
return v___x_1504_;
}
}
else
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = lean_usize_of_nat(v___x_1495_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v___f_1499_, v_vs_1492_, v___x_1505_, v___x_1506_, v___x_1496_);
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1508_, lean_object* v_f_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1508_, v_f_1509_, v___y_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1513_, lean_object* v_m_1514_, lean_object* v_inst_1515_, lean_object* v_f_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1515_, v_f_1516_, v_x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_apply_1(v_f_1519_, v___y_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1523_, lean_object* v_toPure_1524_, lean_object* v_inst_1525_, lean_object* v___f_1526_, lean_object* v_x_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_array_get_size(v_tail_1523_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_nat_dec_lt(v___x_1528_, v___x_1529_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec(v___f_1526_);
lean_dec_ref(v_inst_1525_);
lean_dec_ref(v_tail_1523_);
v___x_1532_ = lean_apply_2(v_toPure_1524_, lean_box(0), v___x_1530_);
return v___x_1532_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_nat_dec_le(v___x_1529_, v___x_1529_);
if (v___x_1533_ == 0)
{
if (v___x_1531_ == 0)
{
lean_object* v___x_1534_; 
lean_dec(v___f_1526_);
lean_dec_ref(v_inst_1525_);
lean_dec_ref(v_tail_1523_);
v___x_1534_ = lean_apply_2(v_toPure_1524_, lean_box(0), v___x_1530_);
return v___x_1534_;
}
else
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_toPure_1524_);
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = lean_usize_of_nat(v___x_1529_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1525_, v___f_1526_, v_tail_1523_, v___x_1535_, v___x_1536_, v___x_1530_);
return v___x_1537_;
}
}
else
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v_toPure_1524_);
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = lean_usize_of_nat(v___x_1529_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1525_, v___f_1526_, v_tail_1523_, v___x_1538_, v___x_1539_, v___x_1530_);
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1541_, lean_object* v_t_1542_, lean_object* v_f_1543_){
_start:
{
lean_object* v_toApplicative_1544_; lean_object* v_toPure_1545_; lean_object* v_toSeqRight_1546_; lean_object* v_root_1547_; lean_object* v_tail_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_toApplicative_1544_ = lean_ctor_get(v_inst_1541_, 0);
v_toPure_1545_ = lean_ctor_get(v_toApplicative_1544_, 1);
v_toSeqRight_1546_ = lean_ctor_get(v_toApplicative_1544_, 4);
lean_inc(v_toSeqRight_1546_);
v_root_1547_ = lean_ctor_get(v_t_1542_, 0);
lean_inc_ref(v_root_1547_);
v_tail_1548_ = lean_ctor_get(v_t_1542_, 1);
lean_inc_ref(v_tail_1548_);
lean_dec_ref(v_t_1542_);
lean_inc(v_f_1543_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1549_, 0, v_f_1543_);
lean_inc_ref(v_inst_1541_);
lean_inc(v_toPure_1545_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1550_, 0, v_tail_1548_);
lean_closure_set(v___f_1550_, 1, v_toPure_1545_);
lean_closure_set(v___f_1550_, 2, v_inst_1541_);
lean_closure_set(v___f_1550_, 3, v___f_1549_);
v___x_1551_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1541_, v_f_1543_, v_root_1547_);
v___x_1552_ = lean_apply_4(v_toSeqRight_1546_, lean_box(0), lean_box(0), v___x_1551_, v___f_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1553_, lean_object* v_m_1554_, lean_object* v_inst_1555_, lean_object* v_t_1556_, lean_object* v_f_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1555_, v_t_1556_, v_f_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_toApplicative_1559_, lean_object* v_j_1560_, lean_object* v_cs_1561_, lean_object* v_inst_1562_, lean_object* v___f_1563_, lean_object* v_____r_1564_){
_start:
{
lean_object* v_toPure_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_toPure_1565_ = lean_ctor_get(v_toApplicative_1559_, 1);
lean_inc(v_toPure_1565_);
lean_dec_ref(v_toApplicative_1559_);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_add(v_j_1560_, v___x_1566_);
v___x_1568_ = lean_array_get_size(v_cs_1561_);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_nat_dec_lt(v___x_1567_, v___x_1568_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v___x_1567_);
lean_dec(v___f_1563_);
lean_dec_ref(v_inst_1562_);
lean_dec_ref(v_cs_1561_);
v___x_1571_ = lean_apply_2(v_toPure_1565_, lean_box(0), v___x_1569_);
return v___x_1571_;
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_le(v___x_1568_, v___x_1568_);
if (v___x_1572_ == 0)
{
if (v___x_1570_ == 0)
{
lean_object* v___x_1573_; 
lean_dec(v___x_1567_);
lean_dec(v___f_1563_);
lean_dec_ref(v_inst_1562_);
lean_dec_ref(v_cs_1561_);
v___x_1573_ = lean_apply_2(v_toPure_1565_, lean_box(0), v___x_1569_);
return v___x_1573_;
}
else
{
size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v_toPure_1565_);
v___x_1574_ = lean_usize_of_nat(v___x_1567_);
lean_dec(v___x_1567_);
v___x_1575_ = lean_usize_of_nat(v___x_1568_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1562_, v___f_1563_, v_cs_1561_, v___x_1574_, v___x_1575_, v___x_1569_);
return v___x_1576_;
}
}
else
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_toPure_1565_);
v___x_1577_ = lean_usize_of_nat(v___x_1567_);
lean_dec(v___x_1567_);
v___x_1578_ = lean_usize_of_nat(v___x_1568_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1562_, v___f_1563_, v_cs_1561_, v___x_1577_, v___x_1578_, v___x_1569_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_1580_, lean_object* v_j_1581_, lean_object* v_cs_1582_, lean_object* v_inst_1583_, lean_object* v___f_1584_, lean_object* v_____r_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_toApplicative_1580_, v_j_1581_, v_cs_1582_, v_inst_1583_, v___f_1584_, v_____r_1585_);
lean_dec(v_j_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1587_, lean_object* v_f_1588_, lean_object* v_x_1589_, size_t v_x_1590_, size_t v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1589_) == 0)
{
lean_object* v_toApplicative_1592_; lean_object* v_toBind_1593_; lean_object* v_cs_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; size_t v___x_1597_; lean_object* v_j_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_toApplicative_1592_ = lean_ctor_get(v_inst_1587_, 0);
v_toBind_1593_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc(v_toBind_1593_);
v_cs_1594_ = lean_ctor_get(v_x_1589_, 0);
lean_inc_ref_n(v_cs_1594_, 2);
lean_dec_ref_known(v_x_1589_, 1);
lean_inc(v_f_1588_);
lean_inc_ref_n(v_inst_1587_, 2);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1595_, 0, v_inst_1587_);
lean_closure_set(v___f_1595_, 1, v_f_1588_);
v___x_1596_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1597_ = lean_usize_shift_right(v_x_1590_, v_x_1591_);
v_j_1598_ = lean_usize_to_nat(v___x_1597_);
lean_inc(v_j_1598_);
lean_inc_ref(v_toApplicative_1592_);
v___f_1599_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1599_, 0, v_toApplicative_1592_);
lean_closure_set(v___f_1599_, 1, v_j_1598_);
lean_closure_set(v___f_1599_, 2, v_cs_1594_);
lean_closure_set(v___f_1599_, 3, v_inst_1587_);
lean_closure_set(v___f_1599_, 4, v___f_1595_);
v___x_1600_ = lean_array_get(v___x_1596_, v_cs_1594_, v_j_1598_);
lean_dec(v_j_1598_);
lean_dec_ref(v_cs_1594_);
v___x_1601_ = ((size_t)1ULL);
v___x_1602_ = lean_usize_shift_left(v___x_1601_, v_x_1591_);
v___x_1603_ = lean_usize_sub(v___x_1602_, v___x_1601_);
v___x_1604_ = lean_usize_land(v_x_1590_, v___x_1603_);
v___x_1605_ = ((size_t)5ULL);
v___x_1606_ = lean_usize_sub(v_x_1591_, v___x_1605_);
v___x_1607_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1587_, v_f_1588_, v___x_1600_, v___x_1604_, v___x_1606_);
v___x_1608_ = lean_apply_4(v_toBind_1593_, lean_box(0), lean_box(0), v___x_1607_, v___f_1599_);
return v___x_1608_;
}
else
{
lean_object* v_toApplicative_1609_; lean_object* v_vs_1610_; lean_object* v_toPure_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_toApplicative_1609_ = lean_ctor_get(v_inst_1587_, 0);
v_vs_1610_ = lean_ctor_get(v_x_1589_, 0);
lean_inc_ref(v_vs_1610_);
lean_dec_ref_known(v_x_1589_, 1);
v_toPure_1611_ = lean_ctor_get(v_toApplicative_1609_, 1);
v___x_1612_ = lean_usize_to_nat(v_x_1590_);
v___x_1613_ = lean_array_get_size(v_vs_1610_);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_nat_dec_lt(v___x_1612_, v___x_1613_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
lean_inc(v_toPure_1611_);
lean_dec(v___x_1612_);
lean_dec_ref(v_vs_1610_);
lean_dec(v_f_1588_);
lean_dec_ref(v_inst_1587_);
v___x_1616_ = lean_apply_2(v_toPure_1611_, lean_box(0), v___x_1614_);
return v___x_1616_;
}
else
{
lean_object* v___f_1617_; uint8_t v___x_1618_; 
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1617_, 0, v_f_1588_);
v___x_1618_ = lean_nat_dec_le(v___x_1613_, v___x_1613_);
if (v___x_1618_ == 0)
{
if (v___x_1615_ == 0)
{
lean_object* v___x_1619_; 
lean_inc(v_toPure_1611_);
lean_dec_ref(v___f_1617_);
lean_dec(v___x_1612_);
lean_dec_ref(v_vs_1610_);
lean_dec_ref(v_inst_1587_);
v___x_1619_ = lean_apply_2(v_toPure_1611_, lean_box(0), v___x_1614_);
return v___x_1619_;
}
else
{
size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_usize_of_nat(v___x_1612_);
lean_dec(v___x_1612_);
v___x_1621_ = lean_usize_of_nat(v___x_1613_);
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1587_, v___f_1617_, v_vs_1610_, v___x_1620_, v___x_1621_, v___x_1614_);
return v___x_1622_;
}
}
else
{
size_t v___x_1623_; size_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_usize_of_nat(v___x_1612_);
lean_dec(v___x_1612_);
v___x_1624_ = lean_usize_of_nat(v___x_1613_);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1587_, v___f_1617_, v_vs_1610_, v___x_1623_, v___x_1624_, v___x_1614_);
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1626_, lean_object* v_f_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
size_t v_x_272__boxed_1631_; size_t v_x_273__boxed_1632_; lean_object* v_res_1633_; 
v_x_272__boxed_1631_ = lean_unbox_usize(v_x_1629_);
lean_dec(v_x_1629_);
v_x_273__boxed_1632_ = lean_unbox_usize(v_x_1630_);
lean_dec(v_x_1630_);
v_res_1633_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1626_, v_f_1627_, v_x_1628_, v_x_272__boxed_1631_, v_x_273__boxed_1632_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1634_, lean_object* v_m_1635_, lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_x_1638_, size_t v_x_1639_, size_t v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1636_, v_f_1637_, v_x_1638_, v_x_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_m_1643_, lean_object* v_inst_1644_, lean_object* v_f_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
size_t v_x_342__boxed_1649_; size_t v_x_343__boxed_1650_; lean_object* v_res_1651_; 
v_x_342__boxed_1649_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_x_343__boxed_1650_ = lean_unbox_usize(v_x_1648_);
lean_dec(v_x_1648_);
v_res_1651_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1642_, v_m_1643_, v_inst_1644_, v_f_1645_, v_x_1646_, v_x_342__boxed_1649_, v_x_343__boxed_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_toApplicative_1652_, lean_object* v_tail_1653_, lean_object* v___x_1654_, lean_object* v_inst_1655_, lean_object* v___f_1656_, lean_object* v_____r_1657_){
_start:
{
lean_object* v_toPure_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_toPure_1658_ = lean_ctor_get(v_toApplicative_1652_, 1);
lean_inc(v_toPure_1658_);
lean_dec_ref(v_toApplicative_1652_);
v___x_1659_ = lean_array_get_size(v_tail_1653_);
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_nat_dec_lt(v___x_1654_, v___x_1659_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v___f_1656_);
lean_dec_ref(v_inst_1655_);
lean_dec_ref(v_tail_1653_);
v___x_1662_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1660_);
return v___x_1662_;
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_nat_dec_le(v___x_1659_, v___x_1659_);
if (v___x_1663_ == 0)
{
if (v___x_1661_ == 0)
{
lean_object* v___x_1664_; 
lean_dec(v___f_1656_);
lean_dec_ref(v_inst_1655_);
lean_dec_ref(v_tail_1653_);
v___x_1664_ = lean_apply_2(v_toPure_1658_, lean_box(0), v___x_1660_);
return v___x_1664_;
}
else
{
size_t v___x_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_toPure_1658_);
v___x_1665_ = ((size_t)0ULL);
v___x_1666_ = lean_usize_of_nat(v___x_1659_);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1655_, v___f_1656_, v_tail_1653_, v___x_1665_, v___x_1666_, v___x_1660_);
return v___x_1667_;
}
}
else
{
size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v_toPure_1658_);
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = lean_usize_of_nat(v___x_1659_);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1655_, v___f_1656_, v_tail_1653_, v___x_1668_, v___x_1669_, v___x_1660_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_toApplicative_1671_, lean_object* v_tail_1672_, lean_object* v___x_1673_, lean_object* v_inst_1674_, lean_object* v___f_1675_, lean_object* v_____r_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_toApplicative_1671_, v_tail_1672_, v___x_1673_, v_inst_1674_, v___f_1675_, v_____r_1676_);
lean_dec(v___x_1673_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1678_, lean_object* v_t_1679_, lean_object* v_f_1680_, lean_object* v_start_1681_){
_start:
{
lean_object* v_toApplicative_1682_; lean_object* v_toBind_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_toApplicative_1682_ = lean_ctor_get(v_inst_1678_, 0);
v_toBind_1683_ = lean_ctor_get(v_inst_1678_, 1);
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_nat_dec_eq(v_start_1681_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v_root_1686_; lean_object* v_tail_1687_; size_t v_shift_1688_; lean_object* v_tailOff_1689_; uint8_t v___x_1690_; 
v_root_1686_ = lean_ctor_get(v_t_1679_, 0);
lean_inc_ref(v_root_1686_);
v_tail_1687_ = lean_ctor_get(v_t_1679_, 1);
lean_inc_ref(v_tail_1687_);
v_shift_1688_ = lean_ctor_get_usize(v_t_1679_, 4);
v_tailOff_1689_ = lean_ctor_get(v_t_1679_, 3);
lean_inc(v_tailOff_1689_);
lean_dec_ref(v_t_1679_);
v___x_1690_ = lean_nat_dec_le(v_tailOff_1689_, v_start_1681_);
if (v___x_1690_ == 0)
{
lean_object* v___f_1691_; lean_object* v___f_1692_; size_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_inc(v_toBind_1683_);
lean_dec(v_tailOff_1689_);
lean_inc(v_f_1680_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1691_, 0, v_f_1680_);
lean_inc_ref(v_inst_1678_);
lean_inc_ref(v_toApplicative_1682_);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1692_, 0, v_toApplicative_1682_);
lean_closure_set(v___f_1692_, 1, v_tail_1687_);
lean_closure_set(v___f_1692_, 2, v___x_1684_);
lean_closure_set(v___f_1692_, 3, v_inst_1678_);
lean_closure_set(v___f_1692_, 4, v___f_1691_);
v___x_1693_ = lean_usize_of_nat(v_start_1681_);
v___x_1694_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1678_, v_f_1680_, v_root_1686_, v___x_1693_, v_shift_1688_);
v___x_1695_ = lean_apply_4(v_toBind_1683_, lean_box(0), lean_box(0), v___x_1694_, v___f_1692_);
return v___x_1695_;
}
else
{
lean_object* v_toPure_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
lean_dec_ref(v_root_1686_);
v_toPure_1696_ = lean_ctor_get(v_toApplicative_1682_, 1);
v___x_1697_ = lean_nat_sub(v_start_1681_, v_tailOff_1689_);
lean_dec(v_tailOff_1689_);
v___x_1698_ = lean_array_get_size(v_tail_1687_);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_nat_dec_lt(v___x_1697_, v___x_1698_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_inc(v_toPure_1696_);
lean_dec(v___x_1697_);
lean_dec_ref(v_tail_1687_);
lean_dec(v_f_1680_);
lean_dec_ref(v_inst_1678_);
v___x_1701_ = lean_apply_2(v_toPure_1696_, lean_box(0), v___x_1699_);
return v___x_1701_;
}
else
{
lean_object* v___f_1702_; uint8_t v___x_1703_; 
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1702_, 0, v_f_1680_);
v___x_1703_ = lean_nat_dec_le(v___x_1698_, v___x_1698_);
if (v___x_1703_ == 0)
{
if (v___x_1700_ == 0)
{
lean_object* v___x_1704_; 
lean_inc(v_toPure_1696_);
lean_dec_ref(v___f_1702_);
lean_dec(v___x_1697_);
lean_dec_ref(v_tail_1687_);
lean_dec_ref(v_inst_1678_);
v___x_1704_ = lean_apply_2(v_toPure_1696_, lean_box(0), v___x_1699_);
return v___x_1704_;
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_usize_of_nat(v___x_1697_);
lean_dec(v___x_1697_);
v___x_1706_ = lean_usize_of_nat(v___x_1698_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1678_, v___f_1702_, v_tail_1687_, v___x_1705_, v___x_1706_, v___x_1699_);
return v___x_1707_;
}
}
else
{
size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_usize_of_nat(v___x_1697_);
lean_dec(v___x_1697_);
v___x_1709_ = lean_usize_of_nat(v___x_1698_);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1678_, v___f_1702_, v_tail_1687_, v___x_1708_, v___x_1709_, v___x_1699_);
return v___x_1710_;
}
}
}
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1678_, v_t_1679_, v_f_1680_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1712_, lean_object* v_t_1713_, lean_object* v_f_1714_, lean_object* v_start_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_PersistentArray_forM___redArg(v_inst_1712_, v_t_1713_, v_f_1714_, v_start_1715_);
lean_dec(v_start_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1717_, lean_object* v_m_1718_, lean_object* v_inst_1719_, lean_object* v_t_1720_, lean_object* v_f_1721_, lean_object* v_start_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_PersistentArray_forM___redArg(v_inst_1719_, v_t_1720_, v_f_1721_, v_start_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_m_1725_, lean_object* v_inst_1726_, lean_object* v_t_1727_, lean_object* v_f_1728_, lean_object* v_start_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_PersistentArray_forM(v_00_u03b1_1724_, v_m_1725_, v_inst_1726_, v_t_1727_, v_f_1728_, v_start_1729_);
lean_dec(v_start_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1731_, lean_object* v_x1_1732_, lean_object* v_x2_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_apply_2(v_f_1731_, v_x1_1732_, v_x2_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1754_, lean_object* v_f_1755_, lean_object* v_init_1756_, lean_object* v_start_1757_){
_start:
{
lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1758_, 0, v_f_1755_);
v___x_1759_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1760_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1759_, v_t_1754_, v___f_1758_, v_init_1756_, v_start_1757_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1761_, lean_object* v_f_1762_, lean_object* v_init_1763_, lean_object* v_start_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_PersistentArray_foldl___redArg(v_t_1761_, v_f_1762_, v_init_1763_, v_start_1764_);
lean_dec(v_start_1764_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_t_1768_, lean_object* v_f_1769_, lean_object* v_init_1770_, lean_object* v_start_1771_){
_start:
{
lean_object* v___f_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1772_, 0, v_f_1769_);
v___x_1773_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1774_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1773_, v_t_1768_, v___f_1772_, v_init_1770_, v_start_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_t_1777_, lean_object* v_f_1778_, lean_object* v_init_1779_, lean_object* v_start_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1775_, v_00_u03b2_1776_, v_t_1777_, v_f_1778_, v_init_1779_, v_start_1780_);
lean_dec(v_start_1780_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1782_, lean_object* v_f_1783_, lean_object* v_init_1784_){
_start:
{
lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1785_, 0, v_f_1783_);
v___x_1786_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1787_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1786_, v_t_1782_, v___f_1785_, v_init_1784_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1788_, lean_object* v_00_u03b2_1789_, lean_object* v_t_1790_, lean_object* v_f_1791_, lean_object* v_init_1792_){
_start:
{
lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1793_, 0, v_f_1791_);
v___x_1794_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1795_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1794_, v_t_1790_, v___f_1793_, v_init_1792_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1796_, lean_object* v_x1_1797_, lean_object* v_x2_1798_){
_start:
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
lean_inc(v_x2_1798_);
v___x_1799_ = lean_apply_1(v_p_1796_, v_x2_1798_);
v___x_1800_ = lean_unbox(v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec(v_x2_1798_);
return v_x1_1797_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_PersistentArray_push___redArg(v_x1_1797_, v_x2_1798_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1802_, lean_object* v_p_1803_){
_start:
{
lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1804_, 0, v_p_1803_);
v___x_1805_ = lean_unsigned_to_nat(32u);
v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
lean_dec_ref(v___x_1806_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1809_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1810_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1809_, v_as_1802_, v___f_1804_, v___x_1808_, v___x_1807_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1811_, lean_object* v_as_1812_, lean_object* v_p_1813_){
_start:
{
lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1814_, 0, v_p_1813_);
v___x_1815_ = lean_unsigned_to_nat(32u);
v___x_1816_ = lean_mk_empty_array_with_capacity(v___x_1815_);
lean_dec_ref(v___x_1816_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1819_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1820_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1819_, v_as_1812_, v___f_1814_, v___x_1818_, v___x_1817_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1821_, size_t v_i_1822_, size_t v_stop_1823_, lean_object* v_b_1824_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_usize_dec_eq(v_i_1822_, v_stop_1823_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; 
v___x_1826_ = lean_array_uget_borrowed(v_as_1821_, v_i_1822_);
lean_inc(v___x_1826_);
v___x_1827_ = lean_array_push(v_b_1824_, v___x_1826_);
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1822_, v___x_1828_);
v_i_1822_ = v___x_1829_;
v_b_1824_ = v___x_1827_;
goto _start;
}
else
{
return v_b_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1831_, lean_object* v_i_1832_, lean_object* v_stop_1833_, lean_object* v_b_1834_){
_start:
{
size_t v_i_boxed_1835_; size_t v_stop_boxed_1836_; lean_object* v_res_1837_; 
v_i_boxed_1835_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_stop_boxed_1836_ = lean_unbox_usize(v_stop_1833_);
lean_dec(v_stop_1833_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1831_, v_i_boxed_1835_, v_stop_boxed_1836_, v_b_1834_);
lean_dec_ref(v_as_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
lean_object* v_cs_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_cs_1840_ = lean_ctor_get(v_x_1838_, 0);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_array_get_size(v_cs_1840_);
v___x_1843_ = lean_nat_dec_lt(v___x_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
return v_x_1839_;
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1842_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1840_, v___x_1844_, v___x_1845_, v_x_1839_);
return v___x_1846_;
}
}
else
{
lean_object* v_vs_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_vs_1847_ = lean_ctor_get(v_x_1838_, 0);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_array_get_size(v_vs_1847_);
v___x_1850_ = lean_nat_dec_lt(v___x_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
return v_x_1839_;
}
else
{
size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1849_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1847_, v___x_1851_, v___x_1852_, v_x_1839_);
return v___x_1853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1854_, size_t v_i_1855_, size_t v_stop_1856_, lean_object* v_b_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_eq(v_i_1855_, v_stop_1856_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; 
v___x_1859_ = lean_array_uget_borrowed(v_as_1854_, v_i_1855_);
v___x_1860_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1859_, v_b_1857_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1855_, v___x_1861_);
v_i_1855_ = v___x_1862_;
v_b_1857_ = v___x_1860_;
goto _start;
}
else
{
return v_b_1857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1864_, lean_object* v_i_1865_, lean_object* v_stop_1866_, lean_object* v_b_1867_){
_start:
{
size_t v_i_boxed_1868_; size_t v_stop_boxed_1869_; lean_object* v_res_1870_; 
v_i_boxed_1868_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_stop_boxed_1869_ = lean_unbox_usize(v_stop_1866_);
lean_dec(v_stop_1866_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1864_, v_i_boxed_1868_, v_stop_boxed_1869_, v_b_1867_);
lean_dec_ref(v_as_1864_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1871_, v_x_1872_);
lean_dec_ref(v_x_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1874_, size_t v_x_1875_, size_t v_x_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_object* v_cs_1878_; lean_object* v___x_1879_; size_t v___x_1880_; lean_object* v_j_1881_; lean_object* v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v_cs_1878_ = lean_ctor_get(v_x_1874_, 0);
v___x_1879_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1880_ = lean_usize_shift_right(v_x_1875_, v_x_1876_);
v_j_1881_ = lean_usize_to_nat(v___x_1880_);
v___x_1882_ = lean_array_get_borrowed(v___x_1879_, v_cs_1878_, v_j_1881_);
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_shift_left(v___x_1883_, v_x_1876_);
v___x_1885_ = lean_usize_sub(v___x_1884_, v___x_1883_);
v___x_1886_ = lean_usize_land(v_x_1875_, v___x_1885_);
v___x_1887_ = ((size_t)5ULL);
v___x_1888_ = lean_usize_sub(v_x_1876_, v___x_1887_);
v___x_1889_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1882_, v___x_1886_, v___x_1888_, v_x_1877_);
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_nat_add(v_j_1881_, v___x_1890_);
lean_dec(v_j_1881_);
v___x_1892_ = lean_array_get_size(v_cs_1878_);
v___x_1893_ = lean_nat_dec_lt(v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_dec(v___x_1891_);
return v___x_1889_;
}
else
{
size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_usize_of_nat(v___x_1891_);
lean_dec(v___x_1891_);
v___x_1895_ = lean_usize_of_nat(v___x_1892_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1878_, v___x_1894_, v___x_1895_, v___x_1889_);
return v___x_1896_;
}
}
else
{
lean_object* v_vs_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v_vs_1897_ = lean_ctor_get(v_x_1874_, 0);
v___x_1898_ = lean_usize_to_nat(v_x_1875_);
v___x_1899_ = lean_array_get_size(v_vs_1897_);
v___x_1900_ = lean_nat_dec_lt(v___x_1898_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_dec(v___x_1898_);
return v_x_1877_;
}
else
{
size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_usize_of_nat(v___x_1898_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_usize_of_nat(v___x_1899_);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1897_, v___x_1901_, v___x_1902_, v_x_1877_);
return v___x_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
size_t v_x_1118__boxed_1908_; size_t v_x_1119__boxed_1909_; lean_object* v_res_1910_; 
v_x_1118__boxed_1908_ = lean_unbox_usize(v_x_1905_);
lean_dec(v_x_1905_);
v_x_1119__boxed_1909_ = lean_unbox_usize(v_x_1906_);
lean_dec(v_x_1906_);
v_res_1910_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1904_, v_x_1118__boxed_1908_, v_x_1119__boxed_1909_, v_x_1907_);
lean_dec_ref(v_x_1904_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1911_, lean_object* v_init_1912_, lean_object* v_start_1913_){
_start:
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_nat_dec_eq(v_start_1913_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v_root_1916_; lean_object* v_tail_1917_; size_t v_shift_1918_; lean_object* v_tailOff_1919_; uint8_t v___x_1920_; 
v_root_1916_ = lean_ctor_get(v_t_1911_, 0);
v_tail_1917_ = lean_ctor_get(v_t_1911_, 1);
v_shift_1918_ = lean_ctor_get_usize(v_t_1911_, 4);
v_tailOff_1919_ = lean_ctor_get(v_t_1911_, 3);
v___x_1920_ = lean_nat_dec_le(v_tailOff_1919_, v_start_1913_);
if (v___x_1920_ == 0)
{
size_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1921_ = lean_usize_of_nat(v_start_1913_);
v___x_1922_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1916_, v___x_1921_, v_shift_1918_, v_init_1912_);
v___x_1923_ = lean_array_get_size(v_tail_1917_);
v___x_1924_ = lean_nat_dec_lt(v___x_1914_, v___x_1923_);
if (v___x_1924_ == 0)
{
return v___x_1922_;
}
else
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = lean_usize_of_nat(v___x_1923_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1917_, v___x_1925_, v___x_1926_, v___x_1922_);
return v___x_1927_;
}
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1928_ = lean_nat_sub(v_start_1913_, v_tailOff_1919_);
v___x_1929_ = lean_array_get_size(v_tail_1917_);
v___x_1930_ = lean_nat_dec_lt(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_dec(v___x_1928_);
return v_init_1912_;
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_usize_of_nat(v___x_1928_);
lean_dec(v___x_1928_);
v___x_1932_ = lean_usize_of_nat(v___x_1929_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1917_, v___x_1931_, v___x_1932_, v_init_1912_);
return v___x_1933_;
}
}
}
else
{
lean_object* v_root_1934_; lean_object* v_tail_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_root_1934_ = lean_ctor_get(v_t_1911_, 0);
v_tail_1935_ = lean_ctor_get(v_t_1911_, 1);
v___x_1936_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1934_, v_init_1912_);
v___x_1937_ = lean_array_get_size(v_tail_1935_);
v___x_1938_ = lean_nat_dec_lt(v___x_1914_, v___x_1937_);
if (v___x_1938_ == 0)
{
return v___x_1936_;
}
else
{
size_t v___x_1939_; size_t v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = lean_usize_of_nat(v___x_1937_);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1935_, v___x_1939_, v___x_1940_, v___x_1936_);
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1942_, lean_object* v_init_1943_, lean_object* v_start_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1942_, v_init_1943_, v_start_1944_);
lean_dec(v_start_1944_);
lean_dec_ref(v_t_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1949_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1946_, v___x_1948_, v___x_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_PersistentArray_toArray___redArg(v_t_1950_);
lean_dec_ref(v_t_1950_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1952_, lean_object* v_t_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_PersistentArray_toArray___redArg(v_t_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1955_, lean_object* v_t_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1955_, v_t_1956_);
lean_dec_ref(v_t_1956_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1958_, lean_object* v_t_1959_, lean_object* v_init_1960_, lean_object* v_start_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1959_, v_init_1960_, v_start_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_t_1964_, lean_object* v_init_1965_, lean_object* v_start_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1963_, v_t_1964_, v_init_1965_, v_start_1966_);
lean_dec(v_start_1966_);
lean_dec_ref(v_t_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1968_, lean_object* v_x_1969_, size_t v_x_1970_, size_t v_x_1971_, lean_object* v_x_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1969_, v_x_1970_, v_x_1971_, v_x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
size_t v_x_1236__boxed_1979_; size_t v_x_1237__boxed_1980_; lean_object* v_res_1981_; 
v_x_1236__boxed_1979_ = lean_unbox_usize(v_x_1976_);
lean_dec(v_x_1976_);
v_x_1237__boxed_1980_ = lean_unbox_usize(v_x_1977_);
lean_dec(v_x_1977_);
v_res_1981_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1974_, v_x_1975_, v_x_1236__boxed_1979_, v_x_1237__boxed_1980_, v_x_1978_);
lean_dec_ref(v_x_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1982_, lean_object* v_as_1983_, size_t v_i_1984_, size_t v_stop_1985_, lean_object* v_b_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1983_, v_i_1984_, v_stop_1985_, v_b_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_stop_1991_, lean_object* v_b_1992_){
_start:
{
size_t v_i_boxed_1993_; size_t v_stop_boxed_1994_; lean_object* v_res_1995_; 
v_i_boxed_1993_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_stop_boxed_1994_ = lean_unbox_usize(v_stop_1991_);
lean_dec(v_stop_1991_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1988_, v_as_1989_, v_i_boxed_1993_, v_stop_boxed_1994_, v_b_1992_);
lean_dec_ref(v_as_1989_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1997_, v_x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_2000_, v_x_2001_, v_x_2002_);
lean_dec_ref(v_x_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2004_, lean_object* v_as_2005_, size_t v_i_2006_, size_t v_stop_2007_, lean_object* v_b_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_2005_, v_i_2006_, v_stop_2007_, v_b_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_as_2011_, lean_object* v_i_2012_, lean_object* v_stop_2013_, lean_object* v_b_2014_){
_start:
{
size_t v_i_boxed_2015_; size_t v_stop_boxed_2016_; lean_object* v_res_2017_; 
v_i_boxed_2015_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_stop_boxed_2016_ = lean_unbox_usize(v_stop_2013_);
lean_dec(v_stop_2013_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_2010_, v_as_2011_, v_i_boxed_2015_, v_stop_boxed_2016_, v_b_2014_);
lean_dec_ref(v_as_2011_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_2018_, size_t v_i_2019_, size_t v_stop_2020_, lean_object* v_b_2021_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_usize_dec_eq(v_i_2019_, v_stop_2020_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; 
v___x_2023_ = lean_array_uget_borrowed(v_as_2018_, v_i_2019_);
lean_inc(v___x_2023_);
v___x_2024_ = l_Lean_PersistentArray_push___redArg(v_b_2021_, v___x_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2019_, v___x_2025_);
v_i_2019_ = v___x_2026_;
v_b_2021_ = v___x_2024_;
goto _start;
}
else
{
return v_b_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_stop_2030_, lean_object* v_b_2031_){
_start:
{
size_t v_i_boxed_2032_; size_t v_stop_boxed_2033_; lean_object* v_res_2034_; 
v_i_boxed_2032_ = lean_unbox_usize(v_i_2029_);
lean_dec(v_i_2029_);
v_stop_boxed_2033_ = lean_unbox_usize(v_stop_2030_);
lean_dec(v_stop_2030_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2028_, v_i_boxed_2032_, v_stop_boxed_2033_, v_b_2031_);
lean_dec_ref(v_as_2028_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2035_) == 0)
{
lean_object* v_cs_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_cs_2037_ = lean_ctor_get(v_x_2035_, 0);
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = lean_array_get_size(v_cs_2037_);
v___x_2040_ = lean_nat_dec_lt(v___x_2038_, v___x_2039_);
if (v___x_2040_ == 0)
{
return v_x_2036_;
}
else
{
size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = ((size_t)0ULL);
v___x_2042_ = lean_usize_of_nat(v___x_2039_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2037_, v___x_2041_, v___x_2042_, v_x_2036_);
return v___x_2043_;
}
}
else
{
lean_object* v_vs_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_vs_2044_ = lean_ctor_get(v_x_2035_, 0);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_array_get_size(v_vs_2044_);
v___x_2047_ = lean_nat_dec_lt(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
return v_x_2036_;
}
else
{
size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = lean_usize_of_nat(v___x_2046_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2044_, v___x_2048_, v___x_2049_, v_x_2036_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2051_, size_t v_i_2052_, size_t v_stop_2053_, lean_object* v_b_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_usize_dec_eq(v_i_2052_, v_stop_2053_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; 
v___x_2056_ = lean_array_uget_borrowed(v_as_2051_, v_i_2052_);
v___x_2057_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2056_, v_b_2054_);
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2052_, v___x_2058_);
v_i_2052_ = v___x_2059_;
v_b_2054_ = v___x_2057_;
goto _start;
}
else
{
return v_b_2054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2061_, lean_object* v_i_2062_, lean_object* v_stop_2063_, lean_object* v_b_2064_){
_start:
{
size_t v_i_boxed_2065_; size_t v_stop_boxed_2066_; lean_object* v_res_2067_; 
v_i_boxed_2065_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_stop_boxed_2066_ = lean_unbox_usize(v_stop_2063_);
lean_dec(v_stop_2063_);
v_res_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2061_, v_i_boxed_2065_, v_stop_boxed_2066_, v_b_2064_);
lean_dec_ref(v_as_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2068_, v_x_2069_);
lean_dec_ref(v_x_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2071_, size_t v_x_2072_, size_t v_x_2073_, lean_object* v_x_2074_){
_start:
{
if (lean_obj_tag(v_x_2071_) == 0)
{
lean_object* v_cs_2075_; lean_object* v___x_2076_; size_t v___x_2077_; lean_object* v_j_2078_; lean_object* v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_cs_2075_ = lean_ctor_get(v_x_2071_, 0);
v___x_2076_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2077_ = lean_usize_shift_right(v_x_2072_, v_x_2073_);
v_j_2078_ = lean_usize_to_nat(v___x_2077_);
v___x_2079_ = lean_array_get_borrowed(v___x_2076_, v_cs_2075_, v_j_2078_);
v___x_2080_ = ((size_t)1ULL);
v___x_2081_ = lean_usize_shift_left(v___x_2080_, v_x_2073_);
v___x_2082_ = lean_usize_sub(v___x_2081_, v___x_2080_);
v___x_2083_ = lean_usize_land(v_x_2072_, v___x_2082_);
v___x_2084_ = ((size_t)5ULL);
v___x_2085_ = lean_usize_sub(v_x_2073_, v___x_2084_);
v___x_2086_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2079_, v___x_2083_, v___x_2085_, v_x_2074_);
v___x_2087_ = lean_unsigned_to_nat(1u);
v___x_2088_ = lean_nat_add(v_j_2078_, v___x_2087_);
lean_dec(v_j_2078_);
v___x_2089_ = lean_array_get_size(v_cs_2075_);
v___x_2090_ = lean_nat_dec_lt(v___x_2088_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec(v___x_2088_);
return v___x_2086_;
}
else
{
size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_usize_of_nat(v___x_2088_);
lean_dec(v___x_2088_);
v___x_2092_ = lean_usize_of_nat(v___x_2089_);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2075_, v___x_2091_, v___x_2092_, v___x_2086_);
return v___x_2093_;
}
}
else
{
lean_object* v_vs_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_vs_2094_ = lean_ctor_get(v_x_2071_, 0);
v___x_2095_ = lean_usize_to_nat(v_x_2072_);
v___x_2096_ = lean_array_get_size(v_vs_2094_);
v___x_2097_ = lean_nat_dec_lt(v___x_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_dec(v___x_2095_);
return v_x_2074_;
}
else
{
size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_usize_of_nat(v___x_2095_);
lean_dec(v___x_2095_);
v___x_2099_ = lean_usize_of_nat(v___x_2096_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2094_, v___x_2098_, v___x_2099_, v_x_2074_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
size_t v_x_1125__boxed_2105_; size_t v_x_1126__boxed_2106_; lean_object* v_res_2107_; 
v_x_1125__boxed_2105_ = lean_unbox_usize(v_x_2102_);
lean_dec(v_x_2102_);
v_x_1126__boxed_2106_ = lean_unbox_usize(v_x_2103_);
lean_dec(v_x_2103_);
v_res_2107_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2101_, v_x_1125__boxed_2105_, v_x_1126__boxed_2106_, v_x_2104_);
lean_dec_ref(v_x_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2108_, lean_object* v_init_2109_, lean_object* v_start_2110_){
_start:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_nat_dec_eq(v_start_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v_root_2113_; lean_object* v_tail_2114_; size_t v_shift_2115_; lean_object* v_tailOff_2116_; uint8_t v___x_2117_; 
v_root_2113_ = lean_ctor_get(v_t_2108_, 0);
v_tail_2114_ = lean_ctor_get(v_t_2108_, 1);
v_shift_2115_ = lean_ctor_get_usize(v_t_2108_, 4);
v_tailOff_2116_ = lean_ctor_get(v_t_2108_, 3);
v___x_2117_ = lean_nat_dec_le(v_tailOff_2116_, v_start_2110_);
if (v___x_2117_ == 0)
{
size_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2118_ = lean_usize_of_nat(v_start_2110_);
v___x_2119_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2113_, v___x_2118_, v_shift_2115_, v_init_2109_);
v___x_2120_ = lean_array_get_size(v_tail_2114_);
v___x_2121_ = lean_nat_dec_lt(v___x_2111_, v___x_2120_);
if (v___x_2121_ == 0)
{
return v___x_2119_;
}
else
{
size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2120_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2114_, v___x_2122_, v___x_2123_, v___x_2119_);
return v___x_2124_;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_nat_sub(v_start_2110_, v_tailOff_2116_);
v___x_2126_ = lean_array_get_size(v_tail_2114_);
v___x_2127_ = lean_nat_dec_lt(v___x_2125_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec(v___x_2125_);
return v_init_2109_;
}
else
{
size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_usize_of_nat(v___x_2125_);
lean_dec(v___x_2125_);
v___x_2129_ = lean_usize_of_nat(v___x_2126_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2114_, v___x_2128_, v___x_2129_, v_init_2109_);
return v___x_2130_;
}
}
}
else
{
lean_object* v_root_2131_; lean_object* v_tail_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v_root_2131_ = lean_ctor_get(v_t_2108_, 0);
v_tail_2132_ = lean_ctor_get(v_t_2108_, 1);
v___x_2133_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2131_, v_init_2109_);
v___x_2134_ = lean_array_get_size(v_tail_2132_);
v___x_2135_ = lean_nat_dec_lt(v___x_2111_, v___x_2134_);
if (v___x_2135_ == 0)
{
return v___x_2133_;
}
else
{
size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_of_nat(v___x_2134_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2132_, v___x_2136_, v___x_2137_, v___x_2133_);
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2139_, lean_object* v_init_2140_, lean_object* v_start_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2139_, v_init_2140_, v_start_2141_);
lean_dec(v_start_2141_);
lean_dec_ref(v_t_2139_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2143_, lean_object* v_t_u2082_2144_){
_start:
{
uint8_t v___x_2145_; 
v___x_2145_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2143_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2144_, v_t_u2081_2143_, v___x_2146_);
return v___x_2147_;
}
else
{
lean_dec_ref(v_t_u2081_2143_);
lean_inc_ref(v_t_u2082_2144_);
return v_t_u2082_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2148_, lean_object* v_t_u2082_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2148_, v_t_u2082_2149_);
lean_dec_ref(v_t_u2082_2149_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2151_, lean_object* v_t_u2081_2152_, lean_object* v_t_u2082_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2152_, v_t_u2082_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_t_u2081_2156_, lean_object* v_t_u2082_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_PersistentArray_append(v_00_u03b1_2155_, v_t_u2081_2156_, v_t_u2082_2157_);
lean_dec_ref(v_t_u2082_2157_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2159_, lean_object* v_t_2160_, lean_object* v_init_2161_, lean_object* v_start_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2160_, v_init_2161_, v_start_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2164_, lean_object* v_t_2165_, lean_object* v_init_2166_, lean_object* v_start_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2164_, v_t_2165_, v_init_2166_, v_start_2167_);
lean_dec(v_start_2167_);
lean_dec_ref(v_t_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2169_, lean_object* v_x_2170_, size_t v_x_2171_, size_t v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2170_, v_x_2171_, v_x_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
size_t v_x_1241__boxed_2180_; size_t v_x_1242__boxed_2181_; lean_object* v_res_2182_; 
v_x_1241__boxed_2180_ = lean_unbox_usize(v_x_2177_);
lean_dec(v_x_2177_);
v_x_1242__boxed_2181_ = lean_unbox_usize(v_x_2178_);
lean_dec(v_x_2178_);
v_res_2182_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2175_, v_x_2176_, v_x_1241__boxed_2180_, v_x_1242__boxed_2181_, v_x_2179_);
lean_dec_ref(v_x_2176_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2183_, lean_object* v_as_2184_, size_t v_i_2185_, size_t v_stop_2186_, lean_object* v_b_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2184_, v_i_2185_, v_stop_2186_, v_b_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_stop_2192_, lean_object* v_b_2193_){
_start:
{
size_t v_i_boxed_2194_; size_t v_stop_boxed_2195_; lean_object* v_res_2196_; 
v_i_boxed_2194_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_stop_boxed_2195_ = lean_unbox_usize(v_stop_2192_);
lean_dec(v_stop_2192_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2189_, v_as_2190_, v_i_boxed_2194_, v_stop_boxed_2195_, v_b_2193_);
lean_dec_ref(v_as_2190_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2198_, v_x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2201_, v_x_2202_, v_x_2203_);
lean_dec_ref(v_x_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2205_, lean_object* v_as_2206_, size_t v_i_2207_, size_t v_stop_2208_, lean_object* v_b_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2206_, v_i_2207_, v_stop_2208_, v_b_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2211_, lean_object* v_as_2212_, lean_object* v_i_2213_, lean_object* v_stop_2214_, lean_object* v_b_2215_){
_start:
{
size_t v_i_boxed_2216_; size_t v_stop_boxed_2217_; lean_object* v_res_2218_; 
v_i_boxed_2216_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_stop_boxed_2217_ = lean_unbox_usize(v_stop_2214_);
lean_dec(v_stop_2214_);
v_res_2218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2211_, v_as_2212_, v_i_boxed_2216_, v_stop_boxed_2217_, v_b_2215_);
lean_dec_ref(v_as_2212_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg(){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg___boxed(lean_object* v___dummy_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_PersistentArray_instAppend___redArg();
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_apply_1(v_f_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2229_, lean_object* v_f_2230_){
_start:
{
lean_object* v___f_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___f_2231_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2231_, 0, v_f_2230_);
v___x_2232_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2233_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2232_, v_t_2229_, v___f_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2234_, lean_object* v_00_u03b2_2235_, lean_object* v_t_2236_, lean_object* v_f_2237_){
_start:
{
lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2238_, 0, v_f_2237_);
v___x_2239_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2240_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2239_, v_t_2236_, v___f_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2241_, lean_object* v_f_2242_){
_start:
{
lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___f_2243_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2243_, 0, v_f_2242_);
v___x_2244_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2245_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2244_, v_t_2241_, v___f_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2246_, lean_object* v_00_u03b2_2247_, lean_object* v_t_2248_, lean_object* v_f_2249_){
_start:
{
lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___f_2250_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2250_, 0, v_f_2249_);
v___x_2251_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2252_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2251_, v_t_2248_, v___f_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2253_, size_t v_i_2254_, size_t v_stop_2255_, lean_object* v_b_2256_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_eq(v_i_2254_, v_stop_2255_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; 
v___x_2258_ = lean_array_uget_borrowed(v_as_2253_, v_i_2254_);
lean_inc(v___x_2258_);
v___x_2259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v_b_2256_);
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2254_, v___x_2260_);
v_i_2254_ = v___x_2261_;
v_b_2256_ = v___x_2259_;
goto _start;
}
else
{
return v_b_2256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2263_, lean_object* v_i_2264_, lean_object* v_stop_2265_, lean_object* v_b_2266_){
_start:
{
size_t v_i_boxed_2267_; size_t v_stop_boxed_2268_; lean_object* v_res_2269_; 
v_i_boxed_2267_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_stop_boxed_2268_ = lean_unbox_usize(v_stop_2265_);
lean_dec(v_stop_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2263_, v_i_boxed_2267_, v_stop_boxed_2268_, v_b_2266_);
lean_dec_ref(v_as_2263_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2270_) == 0)
{
lean_object* v_cs_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_cs_2272_ = lean_ctor_get(v_x_2270_, 0);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_array_get_size(v_cs_2272_);
v___x_2275_ = lean_nat_dec_lt(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
return v_x_2271_;
}
else
{
size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = lean_usize_of_nat(v___x_2274_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2272_, v___x_2276_, v___x_2277_, v_x_2271_);
return v___x_2278_;
}
}
else
{
lean_object* v_vs_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_vs_2279_ = lean_ctor_get(v_x_2270_, 0);
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2281_ = lean_array_get_size(v_vs_2279_);
v___x_2282_ = lean_nat_dec_lt(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
return v_x_2271_;
}
else
{
size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = lean_usize_of_nat(v___x_2281_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2279_, v___x_2283_, v___x_2284_, v_x_2271_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2286_, size_t v_i_2287_, size_t v_stop_2288_, lean_object* v_b_2289_){
_start:
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_usize_dec_eq(v_i_2287_, v_stop_2288_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; size_t v___x_2293_; size_t v___x_2294_; 
v___x_2291_ = lean_array_uget_borrowed(v_as_2286_, v_i_2287_);
v___x_2292_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2291_, v_b_2289_);
v___x_2293_ = ((size_t)1ULL);
v___x_2294_ = lean_usize_add(v_i_2287_, v___x_2293_);
v_i_2287_ = v___x_2294_;
v_b_2289_ = v___x_2292_;
goto _start;
}
else
{
return v_b_2289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2296_, lean_object* v_i_2297_, lean_object* v_stop_2298_, lean_object* v_b_2299_){
_start:
{
size_t v_i_boxed_2300_; size_t v_stop_boxed_2301_; lean_object* v_res_2302_; 
v_i_boxed_2300_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_stop_boxed_2301_ = lean_unbox_usize(v_stop_2298_);
lean_dec(v_stop_2298_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2296_, v_i_boxed_2300_, v_stop_boxed_2301_, v_b_2299_);
lean_dec_ref(v_as_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2303_, v_x_2304_);
lean_dec_ref(v_x_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2306_, size_t v_x_2307_, size_t v_x_2308_, lean_object* v_x_2309_){
_start:
{
if (lean_obj_tag(v_x_2306_) == 0)
{
lean_object* v_cs_2310_; lean_object* v___x_2311_; size_t v___x_2312_; lean_object* v_j_2313_; lean_object* v___x_2314_; size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_cs_2310_ = lean_ctor_get(v_x_2306_, 0);
v___x_2311_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2312_ = lean_usize_shift_right(v_x_2307_, v_x_2308_);
v_j_2313_ = lean_usize_to_nat(v___x_2312_);
v___x_2314_ = lean_array_get_borrowed(v___x_2311_, v_cs_2310_, v_j_2313_);
v___x_2315_ = ((size_t)1ULL);
v___x_2316_ = lean_usize_shift_left(v___x_2315_, v_x_2308_);
v___x_2317_ = lean_usize_sub(v___x_2316_, v___x_2315_);
v___x_2318_ = lean_usize_land(v_x_2307_, v___x_2317_);
v___x_2319_ = ((size_t)5ULL);
v___x_2320_ = lean_usize_sub(v_x_2308_, v___x_2319_);
v___x_2321_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2314_, v___x_2318_, v___x_2320_, v_x_2309_);
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_nat_add(v_j_2313_, v___x_2322_);
lean_dec(v_j_2313_);
v___x_2324_ = lean_array_get_size(v_cs_2310_);
v___x_2325_ = lean_nat_dec_lt(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec(v___x_2323_);
return v___x_2321_;
}
else
{
size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = lean_usize_of_nat(v___x_2323_);
lean_dec(v___x_2323_);
v___x_2327_ = lean_usize_of_nat(v___x_2324_);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2310_, v___x_2326_, v___x_2327_, v___x_2321_);
return v___x_2328_;
}
}
else
{
lean_object* v_vs_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_vs_2329_ = lean_ctor_get(v_x_2306_, 0);
v___x_2330_ = lean_usize_to_nat(v_x_2307_);
v___x_2331_ = lean_array_get_size(v_vs_2329_);
v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec(v___x_2330_);
return v_x_2309_;
}
else
{
size_t v___x_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_usize_of_nat(v___x_2330_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_usize_of_nat(v___x_2331_);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2329_, v___x_2333_, v___x_2334_, v_x_2309_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
size_t v_x_1119__boxed_2340_; size_t v_x_1120__boxed_2341_; lean_object* v_res_2342_; 
v_x_1119__boxed_2340_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_x_1120__boxed_2341_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2342_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2336_, v_x_1119__boxed_2340_, v_x_1120__boxed_2341_, v_x_2339_);
lean_dec_ref(v_x_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2343_, lean_object* v_init_2344_, lean_object* v_start_2345_){
_start:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_nat_dec_eq(v_start_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v_root_2348_; lean_object* v_tail_2349_; size_t v_shift_2350_; lean_object* v_tailOff_2351_; uint8_t v___x_2352_; 
v_root_2348_ = lean_ctor_get(v_t_2343_, 0);
v_tail_2349_ = lean_ctor_get(v_t_2343_, 1);
v_shift_2350_ = lean_ctor_get_usize(v_t_2343_, 4);
v_tailOff_2351_ = lean_ctor_get(v_t_2343_, 3);
v___x_2352_ = lean_nat_dec_le(v_tailOff_2351_, v_start_2345_);
if (v___x_2352_ == 0)
{
size_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2353_ = lean_usize_of_nat(v_start_2345_);
v___x_2354_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2348_, v___x_2353_, v_shift_2350_, v_init_2344_);
v___x_2355_ = lean_array_get_size(v_tail_2349_);
v___x_2356_ = lean_nat_dec_lt(v___x_2346_, v___x_2355_);
if (v___x_2356_ == 0)
{
return v___x_2354_;
}
else
{
size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = lean_usize_of_nat(v___x_2355_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2349_, v___x_2357_, v___x_2358_, v___x_2354_);
return v___x_2359_;
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2360_ = lean_nat_sub(v_start_2345_, v_tailOff_2351_);
v___x_2361_ = lean_array_get_size(v_tail_2349_);
v___x_2362_ = lean_nat_dec_lt(v___x_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_dec(v___x_2360_);
return v_init_2344_;
}
else
{
size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_usize_of_nat(v___x_2360_);
lean_dec(v___x_2360_);
v___x_2364_ = lean_usize_of_nat(v___x_2361_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2349_, v___x_2363_, v___x_2364_, v_init_2344_);
return v___x_2365_;
}
}
}
else
{
lean_object* v_root_2366_; lean_object* v_tail_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_root_2366_ = lean_ctor_get(v_t_2343_, 0);
v_tail_2367_ = lean_ctor_get(v_t_2343_, 1);
v___x_2368_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2366_, v_init_2344_);
v___x_2369_ = lean_array_get_size(v_tail_2367_);
v___x_2370_ = lean_nat_dec_lt(v___x_2346_, v___x_2369_);
if (v___x_2370_ == 0)
{
return v___x_2368_;
}
else
{
size_t v___x_2371_; size_t v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = ((size_t)0ULL);
v___x_2372_ = lean_usize_of_nat(v___x_2369_);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2367_, v___x_2371_, v___x_2372_, v___x_2368_);
return v___x_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2374_, lean_object* v_init_2375_, lean_object* v_start_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2374_, v_init_2375_, v_start_2376_);
lean_dec(v_start_2376_);
lean_dec_ref(v_t_2374_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2379_ = lean_box(0);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2378_, v___x_2379_, v___x_2380_);
v___x_2382_ = l_List_reverse___redArg(v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_PersistentArray_toList___redArg(v_t_2383_);
lean_dec_ref(v_t_2383_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2385_, lean_object* v_t_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_PersistentArray_toList___redArg(v_t_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2388_, lean_object* v_t_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_PersistentArray_toList(v_00_u03b1_2388_, v_t_2389_);
lean_dec_ref(v_t_2389_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2391_, lean_object* v_t_2392_, lean_object* v_init_2393_, lean_object* v_start_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2392_, v_init_2393_, v_start_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_t_2397_, lean_object* v_init_2398_, lean_object* v_start_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2396_, v_t_2397_, v_init_2398_, v_start_2399_);
lean_dec(v_start_2399_);
lean_dec_ref(v_t_2397_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2401_, lean_object* v_x_2402_, size_t v_x_2403_, size_t v_x_2404_, lean_object* v_x_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2402_, v_x_2403_, v_x_2404_, v_x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
size_t v_x_1237__boxed_2412_; size_t v_x_1238__boxed_2413_; lean_object* v_res_2414_; 
v_x_1237__boxed_2412_ = lean_unbox_usize(v_x_2409_);
lean_dec(v_x_2409_);
v_x_1238__boxed_2413_ = lean_unbox_usize(v_x_2410_);
lean_dec(v_x_2410_);
v_res_2414_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2407_, v_x_2408_, v_x_1237__boxed_2412_, v_x_1238__boxed_2413_, v_x_2411_);
lean_dec_ref(v_x_2408_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2415_, lean_object* v_as_2416_, size_t v_i_2417_, size_t v_stop_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2416_, v_i_2417_, v_stop_2418_, v_b_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_stop_2424_, lean_object* v_b_2425_){
_start:
{
size_t v_i_boxed_2426_; size_t v_stop_boxed_2427_; lean_object* v_res_2428_; 
v_i_boxed_2426_ = lean_unbox_usize(v_i_2423_);
lean_dec(v_i_2423_);
v_stop_boxed_2427_ = lean_unbox_usize(v_stop_2424_);
lean_dec(v_stop_2424_);
v_res_2428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2421_, v_as_2422_, v_i_boxed_2426_, v_stop_boxed_2427_, v_b_2425_);
lean_dec_ref(v_as_2422_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2430_, v_x_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2433_, v_x_2434_, v_x_2435_);
lean_dec_ref(v_x_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2437_, lean_object* v_as_2438_, size_t v_i_2439_, size_t v_stop_2440_, lean_object* v_b_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2438_, v_i_2439_, v_stop_2440_, v_b_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2443_, lean_object* v_as_2444_, lean_object* v_i_2445_, lean_object* v_stop_2446_, lean_object* v_b_2447_){
_start:
{
size_t v_i_boxed_2448_; size_t v_stop_boxed_2449_; lean_object* v_res_2450_; 
v_i_boxed_2448_ = lean_unbox_usize(v_i_2445_);
lean_dec(v_i_2445_);
v_stop_boxed_2449_ = lean_unbox_usize(v_stop_2446_);
lean_dec(v_stop_2446_);
v_res_2450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2443_, v_as_2444_, v_i_boxed_2448_, v_stop_boxed_2449_, v_b_2447_);
lean_dec_ref(v_as_2444_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2451_, lean_object* v_p_2452_, lean_object* v_x_2453_){
_start:
{
if (lean_obj_tag(v_x_2453_) == 0)
{
lean_object* v_toApplicative_2454_; lean_object* v_cs_2455_; lean_object* v_toPure_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_toApplicative_2454_ = lean_ctor_get(v_inst_2451_, 0);
v_cs_2455_ = lean_ctor_get(v_x_2453_, 0);
lean_inc_ref(v_cs_2455_);
lean_dec_ref_known(v_x_2453_, 1);
v_toPure_2456_ = lean_ctor_get(v_toApplicative_2454_, 1);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_array_get_size(v_cs_2455_);
v___x_2459_ = lean_nat_dec_lt(v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_inc(v_toPure_2456_);
lean_dec_ref(v_cs_2455_);
lean_dec(v_p_2452_);
lean_dec_ref(v_inst_2451_);
v___x_2460_ = lean_box(v___x_2459_);
v___x_2461_ = lean_apply_2(v_toPure_2456_, lean_box(0), v___x_2460_);
return v___x_2461_;
}
else
{
if (v___x_2459_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_inc(v_toPure_2456_);
lean_dec_ref(v_cs_2455_);
lean_dec(v_p_2452_);
lean_dec_ref(v_inst_2451_);
v___x_2462_ = lean_box(v___x_2459_);
v___x_2463_ = lean_apply_2(v_toPure_2456_, lean_box(0), v___x_2462_);
return v___x_2463_;
}
else
{
lean_object* v___f_2464_; size_t v___x_2465_; size_t v___x_2466_; lean_object* v___x_2467_; 
lean_inc_ref(v_inst_2451_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2464_, 0, v_inst_2451_);
lean_closure_set(v___f_2464_, 1, v_p_2452_);
v___x_2465_ = ((size_t)0ULL);
v___x_2466_ = lean_usize_of_nat(v___x_2458_);
v___x_2467_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2451_, v___f_2464_, v_cs_2455_, v___x_2465_, v___x_2466_);
return v___x_2467_;
}
}
}
else
{
lean_object* v_toApplicative_2468_; lean_object* v_vs_2469_; lean_object* v_toPure_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_toApplicative_2468_ = lean_ctor_get(v_inst_2451_, 0);
v_vs_2469_ = lean_ctor_get(v_x_2453_, 0);
lean_inc_ref(v_vs_2469_);
lean_dec_ref_known(v_x_2453_, 1);
v_toPure_2470_ = lean_ctor_get(v_toApplicative_2468_, 1);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = lean_array_get_size(v_vs_2469_);
v___x_2473_ = lean_nat_dec_lt(v___x_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_inc(v_toPure_2470_);
lean_dec_ref(v_vs_2469_);
lean_dec(v_p_2452_);
lean_dec_ref(v_inst_2451_);
v___x_2474_ = lean_box(v___x_2473_);
v___x_2475_ = lean_apply_2(v_toPure_2470_, lean_box(0), v___x_2474_);
return v___x_2475_;
}
else
{
if (v___x_2473_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_inc(v_toPure_2470_);
lean_dec_ref(v_vs_2469_);
lean_dec(v_p_2452_);
lean_dec_ref(v_inst_2451_);
v___x_2476_ = lean_box(v___x_2473_);
v___x_2477_ = lean_apply_2(v_toPure_2470_, lean_box(0), v___x_2476_);
return v___x_2477_;
}
else
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = lean_usize_of_nat(v___x_2472_);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2451_, v_p_2452_, v_vs_2469_, v___x_2478_, v___x_2479_);
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2481_, lean_object* v_p_2482_, lean_object* v_c_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2481_, v_p_2482_, v_c_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2485_, lean_object* v_m_2486_, lean_object* v_inst_2487_, lean_object* v_p_2488_, lean_object* v_x_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2487_, v_p_2488_, v_x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2491_, lean_object* v_toPure_2492_, lean_object* v_inst_2493_, lean_object* v_p_2494_, uint8_t v_b_2495_){
_start:
{
if (v_b_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = lean_array_get_size(v_tail_2491_);
v___x_2498_ = lean_nat_dec_lt(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v_p_2494_);
lean_dec_ref(v_inst_2493_);
lean_dec_ref(v_tail_2491_);
v___x_2499_ = lean_box(v___x_2498_);
v___x_2500_ = lean_apply_2(v_toPure_2492_, lean_box(0), v___x_2499_);
return v___x_2500_;
}
else
{
if (v___x_2498_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec(v_p_2494_);
lean_dec_ref(v_inst_2493_);
lean_dec_ref(v_tail_2491_);
v___x_2501_ = lean_box(v___x_2498_);
v___x_2502_ = lean_apply_2(v_toPure_2492_, lean_box(0), v___x_2501_);
return v___x_2502_;
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v_toPure_2492_);
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = lean_usize_of_nat(v___x_2497_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2493_, v_p_2494_, v_tail_2491_, v___x_2503_, v___x_2504_);
return v___x_2505_;
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_p_2494_);
lean_dec_ref(v_inst_2493_);
lean_dec_ref(v_tail_2491_);
v___x_2506_ = lean_box(v_b_2495_);
v___x_2507_ = lean_apply_2(v_toPure_2492_, lean_box(0), v___x_2506_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2508_, lean_object* v_toPure_2509_, lean_object* v_inst_2510_, lean_object* v_p_2511_, lean_object* v_b_2512_){
_start:
{
uint8_t v_b_boxed_2513_; lean_object* v_res_2514_; 
v_b_boxed_2513_ = lean_unbox(v_b_2512_);
v_res_2514_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2508_, v_toPure_2509_, v_inst_2510_, v_p_2511_, v_b_boxed_2513_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2515_, lean_object* v_t_2516_, lean_object* v_p_2517_){
_start:
{
lean_object* v_toApplicative_2518_; lean_object* v_toBind_2519_; lean_object* v_root_2520_; lean_object* v_tail_2521_; lean_object* v_toPure_2522_; lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; 
v_toApplicative_2518_ = lean_ctor_get(v_inst_2515_, 0);
v_toBind_2519_ = lean_ctor_get(v_inst_2515_, 1);
lean_inc(v_toBind_2519_);
v_root_2520_ = lean_ctor_get(v_t_2516_, 0);
lean_inc_ref(v_root_2520_);
v_tail_2521_ = lean_ctor_get(v_t_2516_, 1);
lean_inc_ref(v_tail_2521_);
lean_dec_ref(v_t_2516_);
v_toPure_2522_ = lean_ctor_get(v_toApplicative_2518_, 1);
lean_inc(v_toPure_2522_);
lean_inc(v_p_2517_);
lean_inc_ref(v_inst_2515_);
v___x_2523_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2515_, v_p_2517_, v_root_2520_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2524_, 0, v_tail_2521_);
lean_closure_set(v___f_2524_, 1, v_toPure_2522_);
lean_closure_set(v___f_2524_, 2, v_inst_2515_);
lean_closure_set(v___f_2524_, 3, v_p_2517_);
v___x_2525_ = lean_apply_4(v_toBind_2519_, lean_box(0), lean_box(0), v___x_2523_, v___f_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2526_, lean_object* v_m_2527_, lean_object* v_inst_2528_, lean_object* v_t_2529_, lean_object* v_p_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2528_, v_t_2529_, v_p_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2532_, uint8_t v_b_2533_){
_start:
{
if (v_b_2533_ == 0)
{
uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = 1;
v___x_2535_ = lean_box(v___x_2534_);
v___x_2536_ = lean_apply_2(v_toPure_2532_, lean_box(0), v___x_2535_);
return v___x_2536_;
}
else
{
uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = 0;
v___x_2538_ = lean_box(v___x_2537_);
v___x_2539_ = lean_apply_2(v_toPure_2532_, lean_box(0), v___x_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2540_, lean_object* v_b_2541_){
_start:
{
uint8_t v_b_boxed_2542_; lean_object* v_res_2543_; 
v_b_boxed_2542_ = lean_unbox(v_b_2541_);
v_res_2543_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2540_, v_b_boxed_2542_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2544_, lean_object* v_toBind_2545_, lean_object* v___f_2546_, lean_object* v_v_2547_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_apply_1(v_p_2544_, v_v_2547_);
v___x_2549_ = lean_apply_4(v_toBind_2545_, lean_box(0), lean_box(0), v___x_2548_, v___f_2546_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2550_, lean_object* v_a_2551_, lean_object* v_p_2552_){
_start:
{
lean_object* v_toApplicative_2553_; lean_object* v_toBind_2554_; lean_object* v_toPure_2555_; lean_object* v___f_2556_; lean_object* v___f_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_toApplicative_2553_ = lean_ctor_get(v_inst_2550_, 0);
v_toBind_2554_ = lean_ctor_get(v_inst_2550_, 1);
lean_inc_n(v_toBind_2554_, 2);
v_toPure_2555_ = lean_ctor_get(v_toApplicative_2553_, 1);
lean_inc(v_toPure_2555_);
v___f_2556_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2556_, 0, v_toPure_2555_);
lean_inc_ref(v___f_2556_);
v___f_2557_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2557_, 0, v_p_2552_);
lean_closure_set(v___f_2557_, 1, v_toBind_2554_);
lean_closure_set(v___f_2557_, 2, v___f_2556_);
v___x_2558_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2550_, v_a_2551_, v___f_2557_);
v___x_2559_ = lean_apply_4(v_toBind_2554_, lean_box(0), lean_box(0), v___x_2558_, v___f_2556_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2560_, lean_object* v_m_2561_, lean_object* v_inst_2562_, lean_object* v_a_2563_, lean_object* v_p_2564_){
_start:
{
lean_object* v_toApplicative_2565_; lean_object* v_toBind_2566_; lean_object* v_toPure_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_toApplicative_2565_ = lean_ctor_get(v_inst_2562_, 0);
v_toBind_2566_ = lean_ctor_get(v_inst_2562_, 1);
lean_inc_n(v_toBind_2566_, 2);
v_toPure_2567_ = lean_ctor_get(v_toApplicative_2565_, 1);
lean_inc(v_toPure_2567_);
v___f_2568_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2568_, 0, v_toPure_2567_);
lean_inc_ref(v___f_2568_);
v___f_2569_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2569_, 0, v_p_2564_);
lean_closure_set(v___f_2569_, 1, v_toBind_2566_);
lean_closure_set(v___f_2569_, 2, v___f_2568_);
v___x_2570_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2562_, v_a_2563_, v___f_2569_);
v___x_2571_ = lean_apply_4(v_toBind_2566_, lean_box(0), lean_box(0), v___x_2570_, v___f_2568_);
return v___x_2571_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2574_ = lean_apply_1(v_p_2572_, v_x_2573_);
v___x_2575_ = lean_unbox(v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2576_, lean_object* v_x_2577_){
_start:
{
uint8_t v_res_2578_; lean_object* v_r_2579_; 
v_res_2578_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2576_, v_x_2577_);
v_r_2579_ = lean_box(v_res_2578_);
return v_r_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg(lean_object* v_a_2580_, lean_object* v_p_2581_){
_start:
{
lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___f_2582_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2582_, 0, v_p_2581_);
v___x_2583_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2584_ = l_Lean_PersistentArray_anyM___redArg(v___x_2583_, v_a_2580_, v___f_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2585_, lean_object* v_a_2586_, lean_object* v_p_2587_){
_start:
{
lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___f_2588_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2588_, 0, v_p_2587_);
v___x_2589_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2590_ = l_Lean_PersistentArray_anyM___redArg(v___x_2589_, v_a_2586_, v___f_2588_);
v___x_2591_ = lean_unbox(v___x_2590_);
lean_dec(v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2592_, lean_object* v_a_2593_, lean_object* v_p_2594_){
_start:
{
uint8_t v_res_2595_; lean_object* v_r_2596_; 
v_res_2595_ = l_Lean_PersistentArray_any(v_00_u03b1_2592_, v_a_2593_, v_p_2594_);
v_r_2596_ = lean_box(v_res_2595_);
return v_r_2596_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2597_, lean_object* v_x_2598_){
_start:
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = lean_apply_1(v_p_2597_, v_x_2598_);
v___x_2600_ = lean_unbox(v___x_2599_);
if (v___x_2600_ == 0)
{
uint8_t v___x_2601_; 
v___x_2601_ = 1;
return v___x_2601_;
}
else
{
uint8_t v___x_2602_; 
v___x_2602_ = 0;
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2603_, lean_object* v_x_2604_){
_start:
{
uint8_t v_res_2605_; lean_object* v_r_2606_; 
v_res_2605_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2603_, v_x_2604_);
v_r_2606_ = lean_box(v_res_2605_);
return v_r_2606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2607_, lean_object* v_p_2608_){
_start:
{
lean_object* v___f_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___f_2609_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2609_, 0, v_p_2608_);
v___x_2610_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2611_ = l_Lean_PersistentArray_anyM___redArg(v___x_2610_, v_a_2607_, v___f_2609_);
v___x_2612_ = lean_unbox(v___x_2611_);
lean_dec(v___x_2611_);
if (v___x_2612_ == 0)
{
uint8_t v___x_2613_; 
v___x_2613_ = 1;
return v___x_2613_;
}
else
{
uint8_t v___x_2614_; 
v___x_2614_ = 0;
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2615_, lean_object* v_p_2616_){
_start:
{
uint8_t v_res_2617_; lean_object* v_r_2618_; 
v_res_2617_ = l_Lean_PersistentArray_all___redArg(v_a_2615_, v_p_2616_);
v_r_2618_ = lean_box(v_res_2617_);
return v_r_2618_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2619_, lean_object* v_a_2620_, lean_object* v_p_2621_){
_start:
{
lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___f_2622_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2622_, 0, v_p_2621_);
v___x_2623_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2624_ = l_Lean_PersistentArray_anyM___redArg(v___x_2623_, v_a_2620_, v___f_2622_);
v___x_2625_ = lean_unbox(v___x_2624_);
lean_dec(v___x_2624_);
if (v___x_2625_ == 0)
{
uint8_t v___x_2626_; 
v___x_2626_ = 1;
return v___x_2626_;
}
else
{
uint8_t v___x_2627_; 
v___x_2627_ = 0;
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_a_2629_, lean_object* v_p_2630_){
_start:
{
uint8_t v_res_2631_; lean_object* v_r_2632_; 
v_res_2631_ = l_Lean_PersistentArray_all(v_00_u03b1_2628_, v_a_2629_, v_p_2630_);
v_r_2632_ = lean_box(v_res_2631_);
return v_r_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_cs_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_vs_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2639_, lean_object* v_f_2640_, lean_object* v_x_2641_){
_start:
{
if (lean_obj_tag(v_x_2641_) == 0)
{
lean_object* v_toApplicative_2642_; lean_object* v_toFunctor_2643_; lean_object* v_cs_2644_; lean_object* v_map_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; size_t v_sz_2648_; size_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_toApplicative_2642_ = lean_ctor_get(v_inst_2639_, 0);
v_toFunctor_2643_ = lean_ctor_get(v_toApplicative_2642_, 0);
v_cs_2644_ = lean_ctor_get(v_x_2641_, 0);
lean_inc_ref(v_cs_2644_);
lean_dec_ref_known(v_x_2641_, 1);
v_map_2645_ = lean_ctor_get(v_toFunctor_2643_, 0);
lean_inc(v_map_2645_);
v___f_2646_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2639_);
v___f_2647_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2647_, 0, v_inst_2639_);
lean_closure_set(v___f_2647_, 1, v_f_2640_);
v_sz_2648_ = lean_array_size(v_cs_2644_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2639_, v___f_2647_, v_sz_2648_, v___x_2649_, v_cs_2644_);
v___x_2651_ = lean_apply_4(v_map_2645_, lean_box(0), lean_box(0), v___f_2646_, v___x_2650_);
return v___x_2651_;
}
else
{
lean_object* v_toApplicative_2652_; lean_object* v_toFunctor_2653_; lean_object* v_vs_2654_; lean_object* v_map_2655_; lean_object* v___f_2656_; size_t v_sz_2657_; size_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_toApplicative_2652_ = lean_ctor_get(v_inst_2639_, 0);
v_toFunctor_2653_ = lean_ctor_get(v_toApplicative_2652_, 0);
v_vs_2654_ = lean_ctor_get(v_x_2641_, 0);
lean_inc_ref(v_vs_2654_);
lean_dec_ref_known(v_x_2641_, 1);
v_map_2655_ = lean_ctor_get(v_toFunctor_2653_, 0);
lean_inc(v_map_2655_);
v___f_2656_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2657_ = lean_array_size(v_vs_2654_);
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2639_, v_f_2640_, v_sz_2657_, v___x_2658_, v_vs_2654_);
v___x_2660_ = lean_apply_4(v_map_2655_, lean_box(0), lean_box(0), v___f_2656_, v___x_2659_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2661_, lean_object* v_f_2662_, lean_object* v_c_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2661_, v_f_2662_, v_c_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2665_, lean_object* v_m_2666_, lean_object* v_inst_2667_, lean_object* v_00_u03b2_2668_, lean_object* v_f_2669_, lean_object* v_x_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2667_, v_f_2669_, v_x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2672_, lean_object* v_size_2673_, size_t v_shift_2674_, lean_object* v_tailOff_2675_, lean_object* v_toPure_2676_, lean_object* v_tail_2677_){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2678_, 0, v_root_2672_);
lean_ctor_set(v___x_2678_, 1, v_tail_2677_);
lean_ctor_set(v___x_2678_, 2, v_size_2673_);
lean_ctor_set(v___x_2678_, 3, v_tailOff_2675_);
lean_ctor_set_usize(v___x_2678_, 4, v_shift_2674_);
v___x_2679_ = lean_apply_2(v_toPure_2676_, lean_box(0), v___x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2680_, lean_object* v_size_2681_, lean_object* v_shift_2682_, lean_object* v_tailOff_2683_, lean_object* v_toPure_2684_, lean_object* v_tail_2685_){
_start:
{
size_t v_shift_boxed_2686_; lean_object* v_res_2687_; 
v_shift_boxed_2686_ = lean_unbox_usize(v_shift_2682_);
lean_dec(v_shift_2682_);
v_res_2687_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2680_, v_size_2681_, v_shift_boxed_2686_, v_tailOff_2683_, v_toPure_2684_, v_tail_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2688_, size_t v_shift_2689_, lean_object* v_tailOff_2690_, lean_object* v_toPure_2691_, lean_object* v_tail_2692_, lean_object* v_inst_2693_, lean_object* v_f_2694_, lean_object* v_toBind_2695_, lean_object* v_root_2696_){
_start:
{
lean_object* v___x_2697_; lean_object* v___f_2698_; size_t v_sz_2699_; size_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = lean_box_usize(v_shift_2689_);
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2698_, 0, v_root_2696_);
lean_closure_set(v___f_2698_, 1, v_size_2688_);
lean_closure_set(v___f_2698_, 2, v___x_2697_);
lean_closure_set(v___f_2698_, 3, v_tailOff_2690_);
lean_closure_set(v___f_2698_, 4, v_toPure_2691_);
v_sz_2699_ = lean_array_size(v_tail_2692_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2693_, v_f_2694_, v_sz_2699_, v___x_2700_, v_tail_2692_);
v___x_2702_ = lean_apply_4(v_toBind_2695_, lean_box(0), lean_box(0), v___x_2701_, v___f_2698_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2703_, lean_object* v_shift_2704_, lean_object* v_tailOff_2705_, lean_object* v_toPure_2706_, lean_object* v_tail_2707_, lean_object* v_inst_2708_, lean_object* v_f_2709_, lean_object* v_toBind_2710_, lean_object* v_root_2711_){
_start:
{
size_t v_shift_boxed_2712_; lean_object* v_res_2713_; 
v_shift_boxed_2712_ = lean_unbox_usize(v_shift_2704_);
lean_dec(v_shift_2704_);
v_res_2713_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2703_, v_shift_boxed_2712_, v_tailOff_2705_, v_toPure_2706_, v_tail_2707_, v_inst_2708_, v_f_2709_, v_toBind_2710_, v_root_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2714_, lean_object* v_f_2715_, lean_object* v_t_2716_){
_start:
{
lean_object* v_toApplicative_2717_; lean_object* v_toBind_2718_; lean_object* v_root_2719_; lean_object* v_tail_2720_; lean_object* v_size_2721_; size_t v_shift_2722_; lean_object* v_tailOff_2723_; lean_object* v_toPure_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___f_2727_; lean_object* v___x_2728_; 
v_toApplicative_2717_ = lean_ctor_get(v_inst_2714_, 0);
v_toBind_2718_ = lean_ctor_get(v_inst_2714_, 1);
lean_inc_n(v_toBind_2718_, 2);
v_root_2719_ = lean_ctor_get(v_t_2716_, 0);
lean_inc_ref(v_root_2719_);
v_tail_2720_ = lean_ctor_get(v_t_2716_, 1);
lean_inc_ref(v_tail_2720_);
v_size_2721_ = lean_ctor_get(v_t_2716_, 2);
lean_inc(v_size_2721_);
v_shift_2722_ = lean_ctor_get_usize(v_t_2716_, 4);
v_tailOff_2723_ = lean_ctor_get(v_t_2716_, 3);
lean_inc(v_tailOff_2723_);
lean_dec_ref(v_t_2716_);
v_toPure_2724_ = lean_ctor_get(v_toApplicative_2717_, 1);
lean_inc(v_toPure_2724_);
lean_inc(v_f_2715_);
lean_inc_ref(v_inst_2714_);
v___x_2725_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2714_, v_f_2715_, v_root_2719_);
v___x_2726_ = lean_box_usize(v_shift_2722_);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2727_, 0, v_size_2721_);
lean_closure_set(v___f_2727_, 1, v___x_2726_);
lean_closure_set(v___f_2727_, 2, v_tailOff_2723_);
lean_closure_set(v___f_2727_, 3, v_toPure_2724_);
lean_closure_set(v___f_2727_, 4, v_tail_2720_);
lean_closure_set(v___f_2727_, 5, v_inst_2714_);
lean_closure_set(v___f_2727_, 6, v_f_2715_);
lean_closure_set(v___f_2727_, 7, v_toBind_2718_);
v___x_2728_ = lean_apply_4(v_toBind_2718_, lean_box(0), lean_box(0), v___x_2725_, v___f_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2729_, lean_object* v_m_2730_, lean_object* v_inst_2731_, lean_object* v_00_u03b2_2732_, lean_object* v_f_2733_, lean_object* v_t_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2731_, v_f_2733_, v_t_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2736_, lean_object* v_x_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_apply_1(v_f_2736_, v_x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2739_, lean_object* v_t_2740_){
_start:
{
lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___f_2741_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2741_, 0, v_f_2739_);
v___x_2742_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2743_ = l_Lean_PersistentArray_mapM___redArg(v___x_2742_, v___f_2741_, v_t_2740_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2744_, lean_object* v_00_u03b2_2745_, lean_object* v_f_2746_, lean_object* v_t_2747_){
_start:
{
lean_object* v___f_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___f_2748_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2748_, 0, v_f_2746_);
v___x_2749_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2750_ = l_Lean_PersistentArray_mapM___redArg(v___x_2749_, v___f_2748_, v_t_2747_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2751_) == 0)
{
lean_object* v_cs_2754_; lean_object* v_numNodes_2755_; lean_object* v_depth_2756_; lean_object* v_tailSize_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2779_; 
v_cs_2754_ = lean_ctor_get(v_x_2751_, 0);
v_numNodes_2755_ = lean_ctor_get(v_x_2752_, 0);
v_depth_2756_ = lean_ctor_get(v_x_2752_, 1);
v_tailSize_2757_ = lean_ctor_get(v_x_2752_, 2);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_x_2752_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2759_ = v_x_2752_;
v_isShared_2760_ = v_isSharedCheck_2779_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_tailSize_2757_);
lean_inc(v_depth_2756_);
lean_inc(v_numNodes_2755_);
lean_dec(v_x_2752_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2779_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___y_2764_; uint8_t v___x_2778_; 
v___x_2761_ = lean_unsigned_to_nat(1u);
v___x_2762_ = lean_nat_add(v_numNodes_2755_, v___x_2761_);
lean_dec(v_numNodes_2755_);
v___x_2778_ = lean_nat_dec_le(v_x_2753_, v_depth_2756_);
if (v___x_2778_ == 0)
{
lean_dec(v_depth_2756_);
lean_inc(v_x_2753_);
v___y_2764_ = v_x_2753_;
goto v___jp_2763_;
}
else
{
v___y_2764_ = v_depth_2756_;
goto v___jp_2763_;
}
v___jp_2763_:
{
lean_object* v___x_2766_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___y_2764_);
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2766_ = v___x_2759_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___y_2764_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_tailSize_2757_);
v___x_2766_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = lean_array_get_size(v_cs_2754_);
v___x_2769_ = lean_nat_dec_lt(v___x_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_dec(v_x_2753_);
return v___x_2766_;
}
else
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_nat_dec_le(v___x_2768_, v___x_2768_);
if (v___x_2770_ == 0)
{
if (v___x_2769_ == 0)
{
lean_dec(v_x_2753_);
return v___x_2766_;
}
else
{
size_t v___x_2771_; size_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = ((size_t)0ULL);
v___x_2772_ = lean_usize_of_nat(v___x_2768_);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2753_, v_cs_2754_, v___x_2771_, v___x_2772_, v___x_2766_);
lean_dec(v_x_2753_);
return v___x_2773_;
}
}
else
{
size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = lean_usize_of_nat(v___x_2768_);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2753_, v_cs_2754_, v___x_2774_, v___x_2775_, v___x_2766_);
lean_dec(v_x_2753_);
return v___x_2776_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2780_; lean_object* v_depth_2781_; lean_object* v_tailSize_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2795_; 
v_numNodes_2780_ = lean_ctor_get(v_x_2752_, 0);
v_depth_2781_ = lean_ctor_get(v_x_2752_, 1);
v_tailSize_2782_ = lean_ctor_get(v_x_2752_, 2);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_x_2752_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2784_ = v_x_2752_;
v_isShared_2785_ = v_isSharedCheck_2795_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_tailSize_2782_);
lean_inc(v_depth_2781_);
lean_inc(v_numNodes_2780_);
lean_dec(v_x_2752_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2795_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = lean_nat_add(v_numNodes_2780_, v___x_2786_);
lean_dec(v_numNodes_2780_);
v___x_2788_ = lean_nat_dec_le(v_x_2753_, v_depth_2781_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2790_; 
lean_dec(v_depth_2781_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v_x_2753_);
lean_ctor_set(v___x_2784_, 0, v___x_2787_);
v___x_2790_ = v___x_2784_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_x_2753_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_tailSize_2782_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
else
{
lean_object* v___x_2793_; 
lean_dec(v_x_2753_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2787_);
v___x_2793_ = v___x_2784_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_depth_2781_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_tailSize_2782_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2796_, lean_object* v_as_2797_, size_t v_i_2798_, size_t v_stop_2799_, lean_object* v_b_2800_){
_start:
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_usize_dec_eq(v_i_2798_, v_stop_2799_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; 
v___x_2802_ = lean_array_uget_borrowed(v_as_2797_, v_i_2798_);
v___x_2803_ = lean_unsigned_to_nat(1u);
v___x_2804_ = lean_nat_add(v_x_2796_, v___x_2803_);
v___x_2805_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2802_, v_b_2800_, v___x_2804_);
v___x_2806_ = ((size_t)1ULL);
v___x_2807_ = lean_usize_add(v_i_2798_, v___x_2806_);
v_i_2798_ = v___x_2807_;
v_b_2800_ = v___x_2805_;
goto _start;
}
else
{
return v_b_2800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2809_, lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_stop_2812_, lean_object* v_b_2813_){
_start:
{
size_t v_i_boxed_2814_; size_t v_stop_boxed_2815_; lean_object* v_res_2816_; 
v_i_boxed_2814_ = lean_unbox_usize(v_i_2811_);
lean_dec(v_i_2811_);
v_stop_boxed_2815_ = lean_unbox_usize(v_stop_2812_);
lean_dec(v_stop_2812_);
v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2809_, v_as_2810_, v_i_boxed_2814_, v_stop_boxed_2815_, v_b_2813_);
lean_dec_ref(v_as_2810_);
lean_dec(v_x_2809_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2817_, v_x_2818_, v_x_2819_);
lean_dec_ref(v_x_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_, lean_object* v_x_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2822_, v_x_2823_, v_x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2826_, v_x_2827_, v_x_2828_, v_x_2829_);
lean_dec_ref(v_x_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2831_, lean_object* v_x_2832_, lean_object* v_as_2833_, size_t v_i_2834_, size_t v_stop_2835_, lean_object* v_b_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2832_, v_as_2833_, v_i_2834_, v_stop_2835_, v_b_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_x_2839_, lean_object* v_as_2840_, lean_object* v_i_2841_, lean_object* v_stop_2842_, lean_object* v_b_2843_){
_start:
{
size_t v_i_boxed_2844_; size_t v_stop_boxed_2845_; lean_object* v_res_2846_; 
v_i_boxed_2844_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_stop_boxed_2845_ = lean_unbox_usize(v_stop_2842_);
lean_dec(v_stop_2842_);
v_res_2846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2838_, v_x_2839_, v_as_2840_, v_i_boxed_2844_, v_stop_boxed_2845_, v_b_2843_);
lean_dec_ref(v_as_2840_);
lean_dec(v_x_2839_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2847_){
_start:
{
lean_object* v_root_2848_; lean_object* v_tail_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_root_2848_ = lean_ctor_get(v_r_2847_, 0);
v_tail_2849_ = lean_ctor_get(v_r_2847_, 1);
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_array_get_size(v_tail_2849_);
v___x_2852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2850_);
lean_ctor_set(v___x_2852_, 2, v___x_2851_);
v___x_2853_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2848_, v___x_2852_, v___x_2850_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lean_PersistentArray_stats___redArg(v_r_2854_);
lean_dec_ref(v_r_2854_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2856_, lean_object* v_r_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_PersistentArray_stats___redArg(v_r_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2859_, lean_object* v_r_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_PersistentArray_stats(v_00_u03b1_2859_, v_r_2860_);
lean_dec_ref(v_r_2860_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2866_){
_start:
{
lean_object* v_numNodes_2867_; lean_object* v_depth_2868_; lean_object* v_tailSize_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_numNodes_2867_ = lean_ctor_get(v_s_2866_, 0);
lean_inc(v_numNodes_2867_);
v_depth_2868_ = lean_ctor_get(v_s_2866_, 1);
lean_inc(v_depth_2868_);
v_tailSize_2869_ = lean_ctor_get(v_s_2866_, 2);
lean_inc(v_tailSize_2869_);
lean_dec_ref(v_s_2866_);
v___x_2870_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2871_ = l_Nat_reprFast(v_numNodes_2867_);
v___x_2872_ = lean_string_append(v___x_2870_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
v___x_2875_ = l_Nat_reprFast(v_depth_2868_);
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
v___x_2879_ = l_Nat_reprFast(v_tailSize_2869_);
v___x_2880_ = lean_string_append(v___x_2878_, v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2882_ = lean_string_append(v___x_2880_, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2885_, lean_object* v_j_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_zero_2888_; uint8_t v_isZero_2889_; 
v_zero_2888_ = lean_unsigned_to_nat(0u);
v_isZero_2889_ = lean_nat_dec_eq(v_j_2886_, v_zero_2888_);
if (v_isZero_2889_ == 1)
{
lean_dec(v_j_2886_);
lean_dec(v_v_2885_);
return v_a_2887_;
}
else
{
lean_object* v_one_2890_; lean_object* v_n_2891_; lean_object* v___x_2892_; 
v_one_2890_ = lean_unsigned_to_nat(1u);
v_n_2891_ = lean_nat_sub(v_j_2886_, v_one_2890_);
lean_dec(v_j_2886_);
lean_inc(v_v_2885_);
v___x_2892_ = l_Lean_PersistentArray_push___redArg(v_a_2887_, v_v_2885_);
v_j_2886_ = v_n_2891_;
v_a_2887_ = v___x_2892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2894_, lean_object* v_v_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2897_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2895_, v_n_2894_, v___x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2898_, lean_object* v_n_2899_, lean_object* v_v_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_mkPersistentArray___redArg(v_n_2899_, v_v_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2902_, lean_object* v_v_2903_, lean_object* v_n_2904_, lean_object* v_j_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2903_, v_j_2905_, v_a_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2909_, lean_object* v_v_2910_, lean_object* v_n_2911_, lean_object* v_j_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2909_, v_v_2910_, v_n_2911_, v_j_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_n_2911_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2916_, lean_object* v_v_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_mkPersistentArray___redArg(v_n_2916_, v_v_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2919_, lean_object* v_n_2920_, lean_object* v_v_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_mkPersistentArray___redArg(v_n_2920_, v_v_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
if (lean_obj_tag(v_a_2923_) == 0)
{
return v_a_2924_;
}
else
{
lean_object* v_head_2925_; lean_object* v_tail_2926_; lean_object* v___x_2927_; 
v_head_2925_ = lean_ctor_get(v_a_2923_, 0);
lean_inc(v_head_2925_);
v_tail_2926_ = lean_ctor_get(v_a_2923_, 1);
lean_inc(v_tail_2926_);
lean_dec_ref_known(v_a_2923_, 2);
v___x_2927_ = l_Lean_PersistentArray_push___redArg(v_a_2924_, v_head_2925_);
v_a_2923_ = v_tail_2926_;
v_a_2924_ = v___x_2927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object* v_00_u03b1_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_a_2930_, v_a_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object* v_xs_2933_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2934_ = lean_unsigned_to_nat(32u);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2934_);
lean_dec_ref(v___x_2935_);
v___x_2936_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_2937_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_xs_2933_, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object* v_00_u03b1_2938_, lean_object* v_xs_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_List_toPArray_x27___redArg(v_xs_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object* v_xs_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2942_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_array_get_size(v_xs_2941_);
v___x_2945_ = lean_nat_dec_lt(v___x_2943_, v___x_2944_);
if (v___x_2945_ == 0)
{
return v___x_2942_;
}
else
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_nat_dec_le(v___x_2944_, v___x_2944_);
if (v___x_2946_ == 0)
{
if (v___x_2945_ == 0)
{
return v___x_2942_;
}
else
{
size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = ((size_t)0ULL);
v___x_2948_ = lean_usize_of_nat(v___x_2944_);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2941_, v___x_2947_, v___x_2948_, v___x_2942_);
return v___x_2949_;
}
}
else
{
size_t v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = lean_usize_of_nat(v___x_2944_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2941_, v___x_2950_, v___x_2951_, v___x_2942_);
return v___x_2952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2953_);
lean_dec_ref(v_xs_2953_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object* v_00_u03b1_2955_, lean_object* v_xs_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_xs_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Array_toPArray_x27(v_00_u03b1_2958_, v_xs_2959_);
lean_dec_ref(v_xs_2959_);
return v_res_2960_;
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
