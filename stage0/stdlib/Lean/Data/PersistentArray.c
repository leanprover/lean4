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
size_t lean_usize_of_nat(lean_object*);
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
static const lean_array_object l_Lean_instInhabitedPersistentArray_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedPersistentArray_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedPersistentArray_default___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_instInhabitedPersistentArray_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedPersistentArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_empty___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_empty___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object* v_a_52_){
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
static size_t _init_l_Lean_instInhabitedPersistentArray_default___closed__1(void){
_start:
{
lean_object* v___x_74_; size_t v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_usize_of_nat(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___closed__2(void){
_start:
{
size_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = lean_usize_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = ((lean_object*)(l_Lean_instInhabitedPersistentArray_default___closed__0));
v___x_79_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_80_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_77_);
lean_ctor_set(v___x_80_, 3, v___x_77_);
lean_ctor_set_usize(v___x_80_, 4, v___x_76_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__2, &l_Lean_instInhabitedPersistentArray_default___closed__2_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__2);
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
static lean_object* _init_l_Lean_PersistentArray_empty___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_unsigned_to_nat(32u);
v___x_87_ = lean_mk_empty_array_with_capacity(v___x_86_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_PersistentArray_empty___closed__1(void){
_start:
{
size_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = ((size_t)5ULL);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_unsigned_to_nat(32u);
v___x_92_ = lean_mk_empty_array_with_capacity(v___x_91_);
v___x_93_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_94_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_90_);
lean_ctor_set(v___x_94_, 3, v___x_90_);
lean_ctor_set_usize(v___x_94_, 4, v___x_89_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object* v_00_u03b1_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__1, &l_Lean_PersistentArray_empty___closed__1_once, _init_l_Lean_PersistentArray_empty___closed__1);
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object* v_a_97_){
_start:
{
lean_object* v_size_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_size_98_ = lean_ctor_get(v_a_97_, 2);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_nat_dec_eq(v_size_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object* v_a_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_101_);
lean_dec_ref(v_a_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty(lean_object* v_00_u03b1_104_, lean_object* v_a_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object* v_00_u03b1_107_, lean_object* v_a_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_107_, v_a_108_);
lean_dec_ref(v_a_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray(lean_object* v_00_u03b1_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(32u);
v___x_113_ = lean_mk_empty_array_with_capacity(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mul2Shift(size_t v_i_114_, size_t v_shift_115_){
_start:
{
size_t v___x_116_; 
v___x_116_ = lean_usize_shift_left(v_i_114_, v_shift_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mul2Shift___boxed(lean_object* v_i_117_, lean_object* v_shift_118_){
_start:
{
size_t v_i_boxed_119_; size_t v_shift_boxed_120_; size_t v_res_121_; lean_object* v_r_122_; 
v_i_boxed_119_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_shift_boxed_120_ = lean_unbox_usize(v_shift_118_);
lean_dec(v_shift_118_);
v_res_121_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_119_, v_shift_boxed_120_);
v_r_122_ = lean_box_usize(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_div2Shift(size_t v_i_123_, size_t v_shift_124_){
_start:
{
size_t v___x_125_; 
v___x_125_ = lean_usize_shift_right(v_i_123_, v_shift_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_div2Shift___boxed(lean_object* v_i_126_, lean_object* v_shift_127_){
_start:
{
size_t v_i_boxed_128_; size_t v_shift_boxed_129_; size_t v_res_130_; lean_object* v_r_131_; 
v_i_boxed_128_ = lean_unbox_usize(v_i_126_);
lean_dec(v_i_126_);
v_shift_boxed_129_ = lean_unbox_usize(v_shift_127_);
lean_dec(v_shift_127_);
v_res_130_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_128_, v_shift_boxed_129_);
v_r_131_ = lean_box_usize(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mod2Shift(size_t v_i_132_, size_t v_shift_133_){
_start:
{
size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; 
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_shift_left(v___x_134_, v_shift_133_);
v___x_136_ = lean_usize_sub(v___x_135_, v___x_134_);
v___x_137_ = lean_usize_land(v_i_132_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mod2Shift___boxed(lean_object* v_i_138_, lean_object* v_shift_139_){
_start:
{
size_t v_i_boxed_140_; size_t v_shift_boxed_141_; size_t v_res_142_; lean_object* v_r_143_; 
v_i_boxed_140_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_shift_boxed_141_ = lean_unbox_usize(v_shift_139_);
lean_dec(v_shift_139_);
v_res_142_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_140_, v_shift_boxed_141_);
v_r_143_ = lean_box_usize(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg(lean_object* v_inst_144_, lean_object* v_x_145_, size_t v_x_146_, size_t v_x_147_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v_cs_148_; lean_object* v___x_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; 
v_cs_148_ = lean_ctor_get(v_x_145_, 0);
v___x_149_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_150_ = lean_usize_shift_right(v_x_146_, v_x_147_);
v___x_151_ = lean_usize_to_nat(v___x_150_);
v___x_152_ = lean_array_get_borrowed(v___x_149_, v_cs_148_, v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_shift_left(v___x_153_, v_x_147_);
v___x_155_ = lean_usize_sub(v___x_154_, v___x_153_);
v___x_156_ = lean_usize_land(v_x_146_, v___x_155_);
v___x_157_ = ((size_t)5ULL);
v___x_158_ = lean_usize_sub(v_x_147_, v___x_157_);
v_x_145_ = v___x_152_;
v_x_146_ = v___x_156_;
v_x_147_ = v___x_158_;
goto _start;
}
else
{
lean_object* v_vs_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_vs_160_ = lean_ctor_get(v_x_145_, 0);
v___x_161_ = lean_usize_to_nat(v_x_146_);
v___x_162_ = lean_array_get_borrowed(v_inst_144_, v_vs_160_, v___x_161_);
lean_dec(v___x_161_);
lean_inc(v___x_162_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg___boxed(lean_object* v_inst_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
size_t v_x_92__boxed_167_; size_t v_x_93__boxed_168_; lean_object* v_res_169_; 
v_x_92__boxed_167_ = lean_unbox_usize(v_x_165_);
lean_dec(v_x_165_);
v_x_93__boxed_168_ = lean_unbox_usize(v_x_166_);
lean_dec(v_x_166_);
v_res_169_ = l_Lean_PersistentArray_getAux___redArg(v_inst_163_, v_x_164_, v_x_92__boxed_167_, v_x_93__boxed_168_);
lean_dec_ref(v_x_164_);
lean_dec(v_inst_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_x_172_, size_t v_x_173_, size_t v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_PersistentArray_getAux___redArg(v_inst_171_, v_x_172_, v_x_173_, v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___boxed(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
size_t v_x_134__boxed_181_; size_t v_x_135__boxed_182_; lean_object* v_res_183_; 
v_x_134__boxed_181_ = lean_unbox_usize(v_x_179_);
lean_dec(v_x_179_);
v_x_135__boxed_182_ = lean_unbox_usize(v_x_180_);
lean_dec(v_x_180_);
v_res_183_ = l_Lean_PersistentArray_getAux(v_00_u03b1_176_, v_inst_177_, v_x_178_, v_x_134__boxed_181_, v_x_135__boxed_182_);
lean_dec_ref(v_x_178_);
lean_dec(v_inst_177_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object* v_inst_184_, lean_object* v_t_185_, lean_object* v_i_186_){
_start:
{
lean_object* v_root_187_; lean_object* v_tail_188_; size_t v_shift_189_; lean_object* v_tailOff_190_; uint8_t v___x_191_; 
v_root_187_ = lean_ctor_get(v_t_185_, 0);
v_tail_188_ = lean_ctor_get(v_t_185_, 1);
v_shift_189_ = lean_ctor_get_usize(v_t_185_, 4);
v_tailOff_190_ = lean_ctor_get(v_t_185_, 3);
v___x_191_ = lean_nat_dec_le(v_tailOff_190_, v_i_186_);
if (v___x_191_ == 0)
{
size_t v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_usize_of_nat(v_i_186_);
v___x_193_ = l_Lean_PersistentArray_getAux___redArg(v_inst_184_, v_root_187_, v___x_192_, v_shift_189_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_nat_sub(v_i_186_, v_tailOff_190_);
v___x_195_ = lean_array_get_borrowed(v_inst_184_, v_tail_188_, v___x_194_);
lean_dec(v___x_194_);
lean_inc(v___x_195_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg___boxed(lean_object* v_inst_196_, lean_object* v_t_197_, lean_object* v_i_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_196_, v_t_197_, v_i_198_);
lean_dec(v_i_198_);
lean_dec_ref(v_t_197_);
lean_dec(v_inst_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21(lean_object* v_00_u03b1_200_, lean_object* v_inst_201_, lean_object* v_t_202_, lean_object* v_i_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_201_, v_t_202_, v_i_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___boxed(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_t_207_, lean_object* v_i_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_PersistentArray_get_x21(v_00_u03b1_205_, v_inst_206_, v_t_207_, v_i_208_);
lean_dec(v_i_208_);
lean_dec_ref(v_t_207_);
lean_dec(v_inst_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(lean_object* v_inst_210_, lean_object* v_xs_211_, lean_object* v_i_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_210_, v_xs_211_, v_i_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(lean_object* v_inst_215_, lean_object* v_xs_216_, lean_object* v_i_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(v_inst_215_, v_xs_216_, v_i_217_, v_x_218_);
lean_dec(v_i_217_);
lean_dec_ref(v_xs_216_);
lean_dec(v_inst_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(lean_object* v_inst_220_){
_start:
{
lean_object* v___f_221_; 
v___f_221_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_221_, 0, v_inst_220_);
return v___f_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___f_224_; 
v___f_224_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_224_, 0, v_inst_223_);
return v___f_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg(lean_object* v_x_225_, size_t v_x_226_, size_t v_x_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v_cs_229_; size_t v_j_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_cs_229_ = lean_ctor_get(v_x_225_, 0);
v_j_230_ = lean_usize_shift_right(v_x_226_, v_x_227_);
v___x_231_ = lean_usize_to_nat(v_j_230_);
v___x_232_ = lean_array_get_size(v_cs_229_);
v___x_233_ = lean_nat_dec_lt(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_dec(v___x_231_);
lean_dec(v_x_228_);
return v_x_225_;
}
else
{
lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_251_; 
lean_inc_ref(v_cs_229_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_x_225_, 0);
lean_dec(v_unused_252_);
v___x_235_ = v_x_225_;
v_isShared_236_ = v_isSharedCheck_251_;
goto v_resetjp_234_;
}
else
{
lean_dec(v_x_225_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_251_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v_i_240_; size_t v___x_241_; size_t v_shift_242_; lean_object* v_v_243_; lean_object* v___x_244_; lean_object* v_xs_x27_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_shift_left(v___x_237_, v_x_227_);
v___x_239_ = lean_usize_sub(v___x_238_, v___x_237_);
v_i_240_ = lean_usize_land(v_x_226_, v___x_239_);
v___x_241_ = ((size_t)5ULL);
v_shift_242_ = lean_usize_sub(v_x_227_, v___x_241_);
v_v_243_ = lean_array_fget(v_cs_229_, v___x_231_);
v___x_244_ = lean_box(0);
v_xs_x27_245_ = lean_array_fset(v_cs_229_, v___x_231_, v___x_244_);
v___x_246_ = l_Lean_PersistentArray_setAux___redArg(v_v_243_, v_i_240_, v_shift_242_, v_x_228_);
v___x_247_ = lean_array_fset(v_xs_x27_245_, v___x_231_, v___x_246_);
lean_dec(v___x_231_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_247_);
v___x_249_ = v___x_235_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_262_; 
v_vs_253_ = lean_ctor_get(v_x_225_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_262_ == 0)
{
v___x_255_ = v_x_225_;
v_isShared_256_ = v_isSharedCheck_262_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_dec(v_x_225_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_262_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = lean_usize_to_nat(v_x_226_);
v___x_258_ = lean_array_set(v_vs_253_, v___x_257_, v_x_228_);
lean_dec(v___x_257_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_258_);
v___x_260_ = v___x_255_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg___boxed(lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
size_t v_x_77__boxed_267_; size_t v_x_78__boxed_268_; lean_object* v_res_269_; 
v_x_77__boxed_267_ = lean_unbox_usize(v_x_264_);
lean_dec(v_x_264_);
v_x_78__boxed_268_ = lean_unbox_usize(v_x_265_);
lean_dec(v_x_265_);
v_res_269_ = l_Lean_PersistentArray_setAux___redArg(v_x_263_, v_x_77__boxed_267_, v_x_78__boxed_268_, v_x_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux(lean_object* v_00_u03b1_270_, lean_object* v_x_271_, size_t v_x_272_, size_t v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentArray_setAux___redArg(v_x_271_, v_x_272_, v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___boxed(lean_object* v_00_u03b1_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
size_t v_x_147__boxed_281_; size_t v_x_148__boxed_282_; lean_object* v_res_283_; 
v_x_147__boxed_281_ = lean_unbox_usize(v_x_278_);
lean_dec(v_x_278_);
v_x_148__boxed_282_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_res_283_ = l_Lean_PersistentArray_setAux(v_00_u03b1_276_, v_x_277_, v_x_147__boxed_281_, v_x_148__boxed_282_, v_x_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg(lean_object* v_t_284_, lean_object* v_i_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_root_287_; lean_object* v_tail_288_; lean_object* v_size_289_; size_t v_shift_290_; lean_object* v_tailOff_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_306_; 
v_root_287_ = lean_ctor_get(v_t_284_, 0);
v_tail_288_ = lean_ctor_get(v_t_284_, 1);
v_size_289_ = lean_ctor_get(v_t_284_, 2);
v_shift_290_ = lean_ctor_get_usize(v_t_284_, 4);
v_tailOff_291_ = lean_ctor_get(v_t_284_, 3);
v_isSharedCheck_306_ = !lean_is_exclusive(v_t_284_);
if (v_isSharedCheck_306_ == 0)
{
v___x_293_ = v_t_284_;
v_isShared_294_ = v_isSharedCheck_306_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_tailOff_291_);
lean_inc(v_size_289_);
lean_inc(v_tail_288_);
lean_inc(v_root_287_);
lean_dec(v_t_284_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_306_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_le(v_tailOff_291_, v_i_285_);
if (v___x_295_ == 0)
{
size_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_296_ = lean_usize_of_nat(v_i_285_);
v___x_297_ = l_Lean_PersistentArray_setAux___redArg(v_root_287_, v___x_296_, v_shift_290_, v_a_286_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_299_ = v___x_293_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_tail_288_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_size_289_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_tailOff_291_);
lean_ctor_set_usize(v_reuseFailAlloc_300_, 4, v_shift_290_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_301_ = lean_nat_sub(v_i_285_, v_tailOff_291_);
v___x_302_ = lean_array_set(v_tail_288_, v___x_301_, v_a_286_);
lean_dec(v___x_301_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_302_);
v___x_304_ = v___x_293_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_root_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_size_289_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_tailOff_291_);
lean_ctor_set_usize(v_reuseFailAlloc_305_, 4, v_shift_290_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg___boxed(lean_object* v_t_307_, lean_object* v_i_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_PersistentArray_set___redArg(v_t_307_, v_i_308_, v_a_309_);
lean_dec(v_i_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set(lean_object* v_00_u03b1_311_, lean_object* v_t_312_, lean_object* v_i_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentArray_set___redArg(v_t_312_, v_i_313_, v_a_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___boxed(lean_object* v_00_u03b1_316_, lean_object* v_t_317_, lean_object* v_i_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_PersistentArray_set(v_00_u03b1_316_, v_t_317_, v_i_318_, v_a_319_);
lean_dec(v_i_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg(lean_object* v_f_321_, lean_object* v_x_322_, size_t v_x_323_, size_t v_x_324_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_cs_325_; size_t v_j_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_cs_325_ = lean_ctor_get(v_x_322_, 0);
v_j_326_ = lean_usize_shift_right(v_x_323_, v_x_324_);
v___x_327_ = lean_usize_to_nat(v_j_326_);
v___x_328_ = lean_array_get_size(v_cs_325_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec(v___x_327_);
lean_dec(v_f_321_);
return v_x_322_;
}
else
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_347_; 
lean_inc_ref(v_cs_325_);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_x_322_, 0);
lean_dec(v_unused_348_);
v___x_331_ = v_x_322_;
v_isShared_332_ = v_isSharedCheck_347_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_x_322_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_347_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v_i_336_; size_t v___x_337_; size_t v_shift_338_; lean_object* v_v_339_; lean_object* v___x_340_; lean_object* v_xs_x27_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_shift_left(v___x_333_, v_x_324_);
v___x_335_ = lean_usize_sub(v___x_334_, v___x_333_);
v_i_336_ = lean_usize_land(v_x_323_, v___x_335_);
v___x_337_ = ((size_t)5ULL);
v_shift_338_ = lean_usize_sub(v_x_324_, v___x_337_);
v_v_339_ = lean_array_fget(v_cs_325_, v___x_327_);
v___x_340_ = lean_box(0);
v_xs_x27_341_ = lean_array_fset(v_cs_325_, v___x_327_, v___x_340_);
v___x_342_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_321_, v_v_339_, v_i_336_, v_shift_338_);
v___x_343_ = lean_array_fset(v_xs_x27_341_, v___x_327_, v___x_342_);
lean_dec(v___x_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_343_);
v___x_345_ = v___x_331_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_vs_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_vs_349_ = lean_ctor_get(v_x_322_, 0);
v___x_350_ = lean_usize_to_nat(v_x_323_);
v___x_351_ = lean_array_get_size(v_vs_349_);
v___x_352_ = lean_nat_dec_lt(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v___x_350_);
lean_dec(v_f_321_);
return v_x_322_;
}
else
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
lean_inc_ref(v_vs_349_);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v_x_322_, 0);
lean_dec(v_unused_365_);
v___x_354_ = v_x_322_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_x_322_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_v_356_; lean_object* v___x_357_; lean_object* v_xs_x27_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v_v_356_ = lean_array_fget(v_vs_349_, v___x_350_);
v___x_357_ = lean_box(0);
v_xs_x27_358_ = lean_array_fset(v_vs_349_, v___x_350_, v___x_357_);
v___x_359_ = lean_apply_1(v_f_321_, v_v_356_);
v___x_360_ = lean_array_fset(v_xs_x27_358_, v___x_350_, v___x_359_);
lean_dec(v___x_350_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_360_);
v___x_362_ = v___x_354_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg___boxed(lean_object* v_f_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
size_t v_x_92__boxed_370_; size_t v_x_93__boxed_371_; lean_object* v_res_372_; 
v_x_92__boxed_370_ = lean_unbox_usize(v_x_368_);
lean_dec(v_x_368_);
v_x_93__boxed_371_ = lean_unbox_usize(v_x_369_);
lean_dec(v_x_369_);
v_res_372_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_366_, v_x_367_, v_x_92__boxed_370_, v_x_93__boxed_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_f_375_, lean_object* v_x_376_, size_t v_x_377_, size_t v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_375_, v_x_376_, v_x_377_, v_x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___boxed(lean_object* v_00_u03b1_380_, lean_object* v_inst_381_, lean_object* v_f_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
size_t v_x_170__boxed_386_; size_t v_x_171__boxed_387_; lean_object* v_res_388_; 
v_x_170__boxed_386_ = lean_unbox_usize(v_x_384_);
lean_dec(v_x_384_);
v_x_171__boxed_387_ = lean_unbox_usize(v_x_385_);
lean_dec(v_x_385_);
v_res_388_ = l_Lean_PersistentArray_modifyAux(v_00_u03b1_380_, v_inst_381_, v_f_382_, v_x_383_, v_x_170__boxed_386_, v_x_171__boxed_387_);
lean_dec(v_inst_381_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg(lean_object* v_t_389_, lean_object* v_i_390_, lean_object* v_f_391_){
_start:
{
lean_object* v_root_392_; lean_object* v_tail_393_; lean_object* v_size_394_; size_t v_shift_395_; lean_object* v_tailOff_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_420_; 
v_root_392_ = lean_ctor_get(v_t_389_, 0);
v_tail_393_ = lean_ctor_get(v_t_389_, 1);
v_size_394_ = lean_ctor_get(v_t_389_, 2);
v_shift_395_ = lean_ctor_get_usize(v_t_389_, 4);
v_tailOff_396_ = lean_ctor_get(v_t_389_, 3);
v_isSharedCheck_420_ = !lean_is_exclusive(v_t_389_);
if (v_isSharedCheck_420_ == 0)
{
v___x_398_ = v_t_389_;
v_isShared_399_ = v_isSharedCheck_420_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_tailOff_396_);
lean_inc(v_size_394_);
lean_inc(v_tail_393_);
lean_inc(v_root_392_);
lean_dec(v_t_389_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_420_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_le(v_tailOff_396_, v_i_390_);
if (v___x_400_ == 0)
{
size_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_usize_of_nat(v_i_390_);
v___x_402_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_391_, v_root_392_, v___x_401_, v_shift_395_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_402_);
v___x_404_ = v___x_398_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_tail_393_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_size_394_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_tailOff_396_);
lean_ctor_set_usize(v_reuseFailAlloc_405_, 4, v_shift_395_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_nat_sub(v_i_390_, v_tailOff_396_);
v___x_407_ = lean_array_get_size(v_tail_393_);
v___x_408_ = lean_nat_dec_lt(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_410_; 
lean_dec(v___x_406_);
lean_dec(v_f_391_);
if (v_isShared_399_ == 0)
{
v___x_410_ = v___x_398_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_root_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_tail_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_size_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_tailOff_396_);
lean_ctor_set_usize(v_reuseFailAlloc_411_, 4, v_shift_395_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_xs_x27_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v_v_412_ = lean_array_fget(v_tail_393_, v___x_406_);
v___x_413_ = lean_box(0);
v_xs_x27_414_ = lean_array_fset(v_tail_393_, v___x_406_, v___x_413_);
v___x_415_ = lean_apply_1(v_f_391_, v_v_412_);
v___x_416_ = lean_array_fset(v_xs_x27_414_, v___x_406_, v___x_415_);
lean_dec(v___x_406_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_416_);
v___x_418_ = v___x_398_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_root_392_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_size_394_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_tailOff_396_);
lean_ctor_set_usize(v_reuseFailAlloc_419_, 4, v_shift_395_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg___boxed(lean_object* v_t_421_, lean_object* v_i_422_, lean_object* v_f_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_PersistentArray_modify___redArg(v_t_421_, v_i_422_, v_f_423_);
lean_dec(v_i_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_t_427_, lean_object* v_i_428_, lean_object* v_f_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_PersistentArray_modify___redArg(v_t_427_, v_i_428_, v_f_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___boxed(lean_object* v_00_u03b1_431_, lean_object* v_inst_432_, lean_object* v_t_433_, lean_object* v_i_434_, lean_object* v_f_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_PersistentArray_modify(v_00_u03b1_431_, v_inst_432_, v_t_433_, v_i_434_, v_f_435_);
lean_dec(v_i_434_);
lean_dec(v_inst_432_);
return v_res_436_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentArray_mkEmptyArray(lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t v_shift_438_, lean_object* v_a_439_){
_start:
{
size_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_dec_eq(v_shift_438_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_442_ = lean_obj_once(&l_Lean_PersistentArray_mkNewPath___redArg___closed__0, &l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once, _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0);
v___x_443_ = ((size_t)5ULL);
v___x_444_ = lean_usize_sub(v_shift_438_, v___x_443_);
v___x_445_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_444_, v_a_439_);
v___x_446_ = lean_array_push(v___x_442_, v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_a_439_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg___boxed(lean_object* v_shift_449_, lean_object* v_a_450_){
_start:
{
size_t v_shift_boxed_451_; lean_object* v_res_452_; 
v_shift_boxed_451_ = lean_unbox_usize(v_shift_449_);
lean_dec(v_shift_449_);
v_res_452_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_451_, v_a_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath(lean_object* v_00_u03b1_453_, size_t v_shift_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_454_, v_a_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___boxed(lean_object* v_00_u03b1_457_, lean_object* v_shift_458_, lean_object* v_a_459_){
_start:
{
size_t v_shift_boxed_460_; lean_object* v_res_461_; 
v_shift_boxed_460_ = lean_unbox_usize(v_shift_458_);
lean_dec(v_shift_458_);
v_res_461_ = l_Lean_PersistentArray_mkNewPath(v_00_u03b1_457_, v_shift_boxed_460_, v_a_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object* v_x_462_, size_t v_x_463_, size_t v_x_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v_cs_466_; size_t v___x_467_; uint8_t v___x_468_; 
v_cs_466_ = lean_ctor_get(v_x_462_, 0);
v___x_467_ = ((size_t)32ULL);
v___x_468_ = lean_usize_dec_lt(v_x_463_, v___x_467_);
if (v___x_468_ == 0)
{
size_t v_j_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v_shift_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_j_469_ = lean_usize_shift_right(v_x_463_, v_x_464_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_shift_left(v___x_470_, v_x_464_);
v___x_472_ = ((size_t)5ULL);
v_shift_473_ = lean_usize_sub(v_x_464_, v___x_472_);
v___x_474_ = lean_usize_to_nat(v_j_469_);
v___x_475_ = lean_array_get_size(v_cs_466_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_485_; 
lean_inc_ref(v_cs_466_);
lean_dec(v___x_474_);
v_isSharedCheck_485_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_x_462_, 0);
lean_dec(v_unused_486_);
v___x_478_ = v_x_462_;
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
else
{
lean_dec(v_x_462_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_473_, v_x_465_);
v___x_481_ = lean_array_push(v_cs_466_, v___x_480_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_481_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
if (v___x_476_ == 0)
{
lean_dec(v___x_474_);
lean_dec_ref(v_x_465_);
return v_x_462_;
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_500_; 
lean_inc_ref(v_cs_466_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v_x_462_, 0);
lean_dec(v_unused_501_);
v___x_488_ = v_x_462_;
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_x_462_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
size_t v___x_490_; size_t v_i_491_; lean_object* v_v_492_; lean_object* v___x_493_; lean_object* v_xs_x27_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_490_ = lean_usize_sub(v___x_471_, v___x_470_);
v_i_491_ = lean_usize_land(v_x_463_, v___x_490_);
v_v_492_ = lean_array_fget(v_cs_466_, v___x_474_);
v___x_493_ = lean_box(0);
v_xs_x27_494_ = lean_array_fset(v_cs_466_, v___x_474_, v___x_493_);
v___x_495_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_v_492_, v_i_491_, v_shift_473_, v_x_465_);
v___x_496_ = lean_array_fset(v_xs_x27_494_, v___x_474_, v___x_495_);
lean_dec(v___x_474_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_496_);
v___x_498_ = v___x_488_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
else
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
lean_inc_ref(v_cs_466_);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_x_462_, 0);
lean_dec(v_unused_511_);
v___x_503_ = v_x_462_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_dec(v_x_462_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 1);
lean_ctor_set(v___x_503_, 0, v_x_465_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_x_465_);
v___x_506_ = v_reuseFailAlloc_509_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_array_push(v_cs_466_, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
}
else
{
lean_dec_ref(v_x_465_);
return v_x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
size_t v_x_107__boxed_516_; size_t v_x_108__boxed_517_; lean_object* v_res_518_; 
v_x_107__boxed_516_ = lean_unbox_usize(v_x_513_);
lean_dec(v_x_513_);
v_x_108__boxed_517_ = lean_unbox_usize(v_x_514_);
lean_dec(v_x_514_);
v_res_518_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_512_, v_x_107__boxed_516_, v_x_108__boxed_517_, v_x_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object* v_00_u03b1_519_, lean_object* v_x_520_, size_t v_x_521_, size_t v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_520_, v_x_521_, v_x_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object* v_00_u03b1_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_201__boxed_530_; size_t v_x_202__boxed_531_; lean_object* v_res_532_; 
v_x_201__boxed_530_ = lean_unbox_usize(v_x_527_);
lean_dec(v_x_527_);
v_x_202__boxed_531_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_532_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_525_, v_x_526_, v_x_201__boxed_530_, v_x_202__boxed_531_, v_x_529_);
return v_res_532_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_PersistentArray_mkEmptyArray(lean_box(0));
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object* v_t_536_){
_start:
{
lean_object* v_root_537_; lean_object* v_tail_538_; lean_object* v_size_539_; size_t v_shift_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_567_; 
v_root_537_ = lean_ctor_get(v_t_536_, 0);
v_tail_538_ = lean_ctor_get(v_t_536_, 1);
v_size_539_ = lean_ctor_get(v_t_536_, 2);
v_shift_540_ = lean_ctor_get_usize(v_t_536_, 4);
v_isSharedCheck_567_ = !lean_is_exclusive(v_t_536_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_t_536_, 3);
lean_dec(v_unused_568_);
v___x_542_ = v_t_536_;
v_isShared_543_ = v_isSharedCheck_567_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_size_539_);
lean_inc(v_tail_538_);
lean_inc(v_root_537_);
lean_dec(v_t_536_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_567_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_544_ = ((size_t)1ULL);
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_usize_add(v_shift_540_, v___x_545_);
v___x_547_ = lean_usize_shift_left(v___x_544_, v___x_546_);
v___x_548_ = lean_usize_to_nat(v___x_547_);
v___x_549_ = lean_nat_dec_le(v_size_539_, v___x_548_);
lean_dec(v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v_n_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_550_ = lean_obj_once(&l_Lean_PersistentArray_mkNewPath___redArg___closed__0, &l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once, _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0);
v_n_551_ = lean_array_push(v___x_550_, v_root_537_);
v___x_552_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_540_, v_tail_538_);
v___x_553_ = lean_array_push(v_n_551_, v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
lean_inc(v_size_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 3, v_size_539_);
lean_ctor_set(v___x_542_, 1, v___x_555_);
lean_ctor_set(v___x_542_, 0, v___x_554_);
v___x_557_ = v___x_542_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_size_539_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_size_539_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_ctor_set_usize(v___x_557_, 4, v___x_546_);
return v___x_557_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; size_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_sub(v_size_539_, v___x_559_);
v___x_561_ = lean_usize_of_nat(v___x_560_);
lean_dec(v___x_560_);
v___x_562_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_root_537_, v___x_561_, v_shift_540_, v_tail_538_);
v___x_563_ = lean_obj_once(&l_Lean_PersistentArray_mkNewTail___redArg___closed__1, &l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once, _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1);
lean_inc(v_size_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 3, v_size_539_);
lean_ctor_set(v___x_542_, 1, v___x_563_);
lean_ctor_set(v___x_542_, 0, v___x_562_);
v___x_565_ = v___x_542_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_size_539_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_size_539_);
lean_ctor_set_usize(v_reuseFailAlloc_566_, 4, v_shift_540_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object* v_00_u03b1_569_, lean_object* v_t_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__0(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = l_System_Platform_numBits;
v___x_573_ = lean_unsigned_to_nat(2u);
v___x_574_ = lean_nat_pow(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(3u);
v___x_576_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__0, &l_Lean_PersistentArray_tooBig___closed__0_once, _init_l_Lean_PersistentArray_tooBig___closed__0);
v___x_577_ = lean_nat_shiftr(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__1, &l_Lean_PersistentArray_tooBig___closed__1_once, _init_l_Lean_PersistentArray_tooBig___closed__1);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object* v_t_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_root_581_; lean_object* v_tail_582_; lean_object* v_size_583_; size_t v_shift_584_; lean_object* v_tailOff_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_603_; 
v_root_581_ = lean_ctor_get(v_t_579_, 0);
v_tail_582_ = lean_ctor_get(v_t_579_, 1);
v_size_583_ = lean_ctor_get(v_t_579_, 2);
v_shift_584_ = lean_ctor_get_usize(v_t_579_, 4);
v_tailOff_585_ = lean_ctor_get(v_t_579_, 3);
v_isSharedCheck_603_ = !lean_is_exclusive(v_t_579_);
if (v_isSharedCheck_603_ == 0)
{
v___x_587_ = v_t_579_;
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_tailOff_585_);
lean_inc(v_size_583_);
lean_inc(v_tail_582_);
lean_inc(v_root_581_);
lean_dec(v_t_579_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_r_593_; 
v___x_589_ = lean_array_push(v_tail_582_, v_a_580_);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_size_583_, v___x_590_);
lean_inc_ref(v___x_589_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v___x_591_);
lean_ctor_set(v___x_587_, 1, v___x_589_);
v_r_593_ = v___x_587_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_root_581_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_tailOff_585_);
lean_ctor_set_usize(v_reuseFailAlloc_602_, 4, v_shift_584_);
v_r_593_ = v_reuseFailAlloc_602_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
uint8_t v___y_595_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = lean_array_get_size(v___x_589_);
lean_dec_ref(v___x_589_);
v___x_598_ = lean_unsigned_to_nat(32u);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = l_Lean_PersistentArray_tooBig;
v___x_601_ = lean_nat_dec_le(v___x_600_, v_size_583_);
lean_dec(v_size_583_);
v___y_595_ = v___x_601_;
goto v___jp_594_;
}
else
{
lean_dec(v_size_583_);
v___y_595_ = v___x_599_;
goto v___jp_594_;
}
v___jp_594_:
{
if (v___y_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_593_);
return v___x_596_;
}
else
{
return v_r_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_604_, lean_object* v_t_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentArray_push___redArg(v_t_605_, v_a_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(32u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_box(0));
return v___x_611_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_cs_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_666_; 
v_cs_616_ = lean_ctor_get(v_x_615_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_666_ == 0)
{
v___x_618_ = v_x_615_;
v_isShared_619_ = v_isSharedCheck_666_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_cs_616_);
lean_dec(v_x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_666_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_array_get_size(v_cs_616_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v_idx_624_; lean_object* v_last_625_; lean_object* v___x_626_; lean_object* v_fst_627_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v_idx_624_ = lean_nat_sub(v___x_620_, v___x_623_);
v_last_625_ = lean_array_fget_borrowed(v_cs_616_, v_idx_624_);
lean_inc(v_last_625_);
v___x_626_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_625_);
v_fst_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_fst_627_);
if (lean_obj_tag(v_fst_627_) == 0)
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_idx_624_);
lean_del_object(v___x_618_);
lean_dec_ref(v_cs_616_);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; lean_object* v_unused_637_; 
v_unused_636_ = lean_ctor_get(v___x_626_, 1);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v___x_626_, 0);
lean_dec(v_unused_637_);
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_663_; 
v_snd_638_ = lean_ctor_get(v___x_626_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_626_, 0);
lean_dec(v_unused_664_);
v___x_640_ = v___x_626_;
v_isShared_641_ = v_isSharedCheck_663_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_dec(v___x_626_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_663_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v_cs_x27_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_642_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v_cs_x27_643_ = lean_array_fset(v_cs_616_, v_idx_624_, v___x_642_);
v___x_644_ = lean_array_get_size(v_snd_638_);
v___x_645_ = lean_nat_dec_eq(v___x_644_, v___x_621_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_snd_638_);
v___x_647_ = v___x_618_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_snd_638_);
v___x_647_ = v_reuseFailAlloc_652_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_array_fset(v_cs_x27_643_, v_idx_624_, v___x_647_);
lean_dec(v_idx_624_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_648_);
v___x_650_ = v___x_640_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v_cs_x27_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
lean_dec(v_snd_638_);
lean_dec(v_idx_624_);
lean_del_object(v___x_618_);
v_cs_x27_653_ = lean_array_pop(v_cs_x27_643_);
v___x_654_ = lean_array_get_size(v_cs_x27_653_);
v___x_655_ = lean_nat_dec_eq(v___x_654_, v___x_621_);
if (v___x_655_ == 0)
{
lean_object* v___x_657_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_cs_x27_653_);
v___x_657_ = v___x_640_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_cs_x27_653_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec_ref(v_cs_x27_653_);
v___x_659_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_659_);
v___x_661_ = v___x_640_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
else
{
lean_object* v___x_665_; 
lean_del_object(v___x_618_);
lean_dec_ref(v_cs_616_);
v___x_665_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__1, &l_Lean_PersistentArray_popLeaf___redArg___closed__1_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1);
return v___x_665_;
}
}
}
else
{
lean_object* v_vs_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_vs_667_ = lean_ctor_get(v_x_615_, 0);
lean_inc_ref(v_vs_667_);
lean_dec_ref(v_x_615_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v_vs_667_);
v___x_669_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_671_, lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_674_){
_start:
{
lean_object* v_root_675_; lean_object* v_tail_676_; lean_object* v_size_677_; size_t v_shift_678_; lean_object* v_tailOff_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_root_675_ = lean_ctor_get(v_t_674_, 0);
v_tail_676_ = lean_ctor_get(v_t_674_, 1);
v_size_677_ = lean_ctor_get(v_t_674_, 2);
v_shift_678_ = lean_ctor_get_usize(v_t_674_, 4);
v_tailOff_679_ = lean_ctor_get(v_t_674_, 3);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_tail_676_);
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v_fst_684_; 
lean_inc_ref(v_root_675_);
v___x_683_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_675_);
v_fst_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_fst_684_);
if (lean_obj_tag(v_fst_684_) == 0)
{
lean_dec_ref(v___x_683_);
return v_t_674_;
}
else
{
lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_717_; 
lean_inc(v_size_677_);
v_isSharedCheck_717_ = !lean_is_exclusive(v_t_674_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; 
v_unused_718_ = lean_ctor_get(v_t_674_, 3);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_t_674_, 2);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_t_674_, 1);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_t_674_, 0);
lean_dec(v_unused_721_);
v___x_686_ = v_t_674_;
v_isShared_687_ = v_isSharedCheck_717_;
goto v_resetjp_685_;
}
else
{
lean_dec(v_t_674_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_717_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_snd_688_; lean_object* v_val_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_716_; 
v_snd_688_ = lean_ctor_get(v___x_683_, 1);
lean_inc(v_snd_688_);
lean_dec_ref(v___x_683_);
v_val_689_ = lean_ctor_get(v_fst_684_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_fst_684_);
if (v_isSharedCheck_716_ == 0)
{
v___x_691_ = v_fst_684_;
v_isShared_692_ = v_isSharedCheck_716_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_val_689_);
lean_dec(v_fst_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_716_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_last_693_; lean_object* v___x_694_; lean_object* v_newSize_695_; lean_object* v___x_696_; lean_object* v_newTailOff_697_; uint8_t v___y_699_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_last_693_ = lean_array_pop(v_val_689_);
v___x_694_ = lean_unsigned_to_nat(1u);
v_newSize_695_ = lean_nat_sub(v_size_677_, v___x_694_);
lean_dec(v_size_677_);
v___x_696_ = lean_array_get_size(v_last_693_);
v_newTailOff_697_ = lean_nat_sub(v_newSize_695_, v___x_696_);
v___x_712_ = lean_array_get_size(v_snd_688_);
v___x_713_ = lean_nat_dec_eq(v___x_712_, v___x_694_);
if (v___x_713_ == 0)
{
v___y_699_ = v___x_713_;
goto v___jp_698_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_array_fget_borrowed(v_snd_688_, v___x_680_);
v___x_715_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_714_);
v___y_699_ = v___x_715_;
goto v___jp_698_;
}
v___jp_698_:
{
if (v___y_699_ == 0)
{
lean_object* v___x_701_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 0);
lean_ctor_set(v___x_691_, 0, v_snd_688_);
v___x_701_ = v___x_691_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_snd_688_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v_newTailOff_697_);
lean_ctor_set(v___x_686_, 2, v_newSize_695_);
lean_ctor_set(v___x_686_, 1, v_last_693_);
lean_ctor_set(v___x_686_, 0, v___x_701_);
v___x_703_ = v___x_686_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_last_693_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_newSize_695_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_newTailOff_697_);
lean_ctor_set_usize(v_reuseFailAlloc_704_, 4, v_shift_678_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_710_; 
lean_del_object(v___x_691_);
v___x_706_ = lean_array_fget(v_snd_688_, v___x_680_);
lean_dec(v_snd_688_);
v___x_707_ = ((size_t)5ULL);
v___x_708_ = lean_usize_sub(v_shift_678_, v___x_707_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v_newTailOff_697_);
lean_ctor_set(v___x_686_, 2, v_newSize_695_);
lean_ctor_set(v___x_686_, 1, v_last_693_);
lean_ctor_set(v___x_686_, 0, v___x_706_);
v___x_710_ = v___x_686_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_last_693_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_newSize_695_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_newTailOff_697_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_ctor_set_usize(v___x_710_, 4, v___x_708_);
return v___x_710_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_731_; 
lean_inc(v_tailOff_679_);
lean_inc(v_size_677_);
lean_inc_ref(v_tail_676_);
lean_inc_ref(v_root_675_);
v_isSharedCheck_731_ = !lean_is_exclusive(v_t_674_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; 
v_unused_732_ = lean_ctor_get(v_t_674_, 3);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_t_674_, 2);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_t_674_, 1);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_t_674_, 0);
lean_dec(v_unused_735_);
v___x_723_ = v_t_674_;
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
else
{
lean_dec(v_t_674_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_725_ = lean_array_pop(v_tail_676_);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_sub(v_size_677_, v___x_726_);
lean_dec(v_size_677_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 2, v___x_727_);
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_root_675_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_tailOff_679_);
lean_ctor_set_usize(v_reuseFailAlloc_730_, 4, v_shift_678_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_736_, lean_object* v_t_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentArray_pop___redArg(v_t_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v_cs_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_cs_743_ = lean_ctor_get(v_x_741_, 0);
lean_inc_ref(v_cs_743_);
lean_dec_ref(v_x_741_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_get_size(v_cs_743_);
v___x_746_ = lean_nat_dec_lt(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v_toApplicative_747_; lean_object* v_toPure_748_; lean_object* v___x_749_; 
lean_dec_ref(v_cs_743_);
lean_dec(v_f_740_);
v_toApplicative_747_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_747_);
lean_dec_ref(v_inst_739_);
v_toPure_748_ = lean_ctor_get(v_toApplicative_747_, 1);
lean_inc(v_toPure_748_);
lean_dec_ref(v_toApplicative_747_);
v___x_749_ = lean_apply_2(v_toPure_748_, lean_box(0), v_x_742_);
return v___x_749_;
}
else
{
lean_object* v___f_750_; uint8_t v___x_751_; 
lean_inc_ref(v_inst_739_);
v___f_750_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_750_, 0, v_inst_739_);
lean_closure_set(v___f_750_, 1, v_f_740_);
v___x_751_ = lean_nat_dec_le(v___x_745_, v___x_745_);
if (v___x_751_ == 0)
{
if (v___x_746_ == 0)
{
lean_object* v_toApplicative_752_; lean_object* v_toPure_753_; lean_object* v___x_754_; 
lean_dec_ref(v___f_750_);
lean_dec_ref(v_cs_743_);
v_toApplicative_752_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_752_);
lean_dec_ref(v_inst_739_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_752_, 1);
lean_inc(v_toPure_753_);
lean_dec_ref(v_toApplicative_752_);
v___x_754_ = lean_apply_2(v_toPure_753_, lean_box(0), v_x_742_);
return v___x_754_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_745_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___f_750_, v_cs_743_, v___x_755_, v___x_756_, v_x_742_);
return v___x_757_;
}
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_745_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___f_750_, v_cs_743_, v___x_758_, v___x_759_, v_x_742_);
return v___x_760_;
}
}
}
else
{
lean_object* v_vs_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_vs_761_ = lean_ctor_get(v_x_741_, 0);
lean_inc_ref(v_vs_761_);
lean_dec_ref(v_x_741_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_array_get_size(v_vs_761_);
v___x_764_ = lean_nat_dec_lt(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v_toApplicative_765_; lean_object* v_toPure_766_; lean_object* v___x_767_; 
lean_dec_ref(v_vs_761_);
lean_dec(v_f_740_);
v_toApplicative_765_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_765_);
lean_dec_ref(v_inst_739_);
v_toPure_766_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_766_);
lean_dec_ref(v_toApplicative_765_);
v___x_767_ = lean_apply_2(v_toPure_766_, lean_box(0), v_x_742_);
return v___x_767_;
}
else
{
uint8_t v___x_768_; 
v___x_768_ = lean_nat_dec_le(v___x_763_, v___x_763_);
if (v___x_768_ == 0)
{
if (v___x_764_ == 0)
{
lean_object* v_toApplicative_769_; lean_object* v_toPure_770_; lean_object* v___x_771_; 
lean_dec_ref(v_vs_761_);
lean_dec(v_f_740_);
v_toApplicative_769_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_769_);
lean_dec_ref(v_inst_739_);
v_toPure_770_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_inc(v_toPure_770_);
lean_dec_ref(v_toApplicative_769_);
v___x_771_ = lean_apply_2(v_toPure_770_, lean_box(0), v_x_742_);
return v___x_771_;
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_763_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v_f_740_, v_vs_761_, v___x_772_, v___x_773_, v_x_742_);
return v___x_774_;
}
}
else
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_763_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v_f_740_, v_vs_761_, v___x_775_, v___x_776_, v_x_742_);
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_778_, lean_object* v_f_779_, lean_object* v_b_780_, lean_object* v_c_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_778_, v_f_779_, v_c_781_, v_b_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_783_, lean_object* v_m_784_, lean_object* v_inst_785_, lean_object* v_00_u03b2_786_, lean_object* v_f_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_785_, v_f_787_, v_x_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_j_791_, lean_object* v_cs_792_, lean_object* v_toApplicative_793_, lean_object* v_inst_794_, lean_object* v___f_795_, lean_object* v_b_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v_j_791_, v___x_797_);
v___x_799_ = lean_array_get_size(v_cs_792_);
v___x_800_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v_toPure_801_; lean_object* v___x_802_; 
lean_dec(v___x_798_);
lean_dec(v___f_795_);
lean_dec_ref(v_inst_794_);
lean_dec_ref(v_cs_792_);
v_toPure_801_ = lean_ctor_get(v_toApplicative_793_, 1);
lean_inc(v_toPure_801_);
lean_dec_ref(v_toApplicative_793_);
v___x_802_ = lean_apply_2(v_toPure_801_, lean_box(0), v_b_796_);
return v___x_802_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_803_ == 0)
{
if (v___x_800_ == 0)
{
lean_object* v_toPure_804_; lean_object* v___x_805_; 
lean_dec(v___x_798_);
lean_dec(v___f_795_);
lean_dec_ref(v_inst_794_);
lean_dec_ref(v_cs_792_);
v_toPure_804_ = lean_ctor_get(v_toApplicative_793_, 1);
lean_inc(v_toPure_804_);
lean_dec_ref(v_toApplicative_793_);
v___x_805_ = lean_apply_2(v_toPure_804_, lean_box(0), v_b_796_);
return v___x_805_;
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_toApplicative_793_);
v___x_806_ = lean_usize_of_nat(v___x_798_);
lean_dec(v___x_798_);
v___x_807_ = lean_usize_of_nat(v___x_799_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_794_, v___f_795_, v_cs_792_, v___x_806_, v___x_807_, v_b_796_);
return v___x_808_;
}
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v_toApplicative_793_);
v___x_809_ = lean_usize_of_nat(v___x_798_);
lean_dec(v___x_798_);
v___x_810_ = lean_usize_of_nat(v___x_799_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_794_, v___f_795_, v_cs_792_, v___x_809_, v___x_810_, v_b_796_);
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_j_812_, lean_object* v_cs_813_, lean_object* v_toApplicative_814_, lean_object* v_inst_815_, lean_object* v___f_816_, lean_object* v_b_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_j_812_, v_cs_813_, v_toApplicative_814_, v_inst_815_, v___f_816_, v_b_817_);
lean_dec(v_j_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_819_, lean_object* v_f_820_, lean_object* v_x_821_, size_t v_x_822_, size_t v_x_823_, lean_object* v_x_824_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v_toApplicative_825_; lean_object* v_toBind_826_; lean_object* v_cs_827_; lean_object* v___f_828_; lean_object* v___x_829_; size_t v___x_830_; lean_object* v_j_831_; lean_object* v___f_832_; lean_object* v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_toApplicative_825_ = lean_ctor_get(v_inst_819_, 0);
v_toBind_826_ = lean_ctor_get(v_inst_819_, 1);
lean_inc(v_toBind_826_);
v_cs_827_ = lean_ctor_get(v_x_821_, 0);
lean_inc_ref_n(v_cs_827_, 2);
lean_dec_ref(v_x_821_);
lean_inc(v_f_820_);
lean_inc_ref_n(v_inst_819_, 2);
v___f_828_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_828_, 0, v_inst_819_);
lean_closure_set(v___f_828_, 1, v_f_820_);
v___x_829_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_830_ = lean_usize_shift_right(v_x_822_, v_x_823_);
v_j_831_ = lean_usize_to_nat(v___x_830_);
lean_inc_ref(v_toApplicative_825_);
lean_inc(v_j_831_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_832_, 0, v_j_831_);
lean_closure_set(v___f_832_, 1, v_cs_827_);
lean_closure_set(v___f_832_, 2, v_toApplicative_825_);
lean_closure_set(v___f_832_, 3, v_inst_819_);
lean_closure_set(v___f_832_, 4, v___f_828_);
v___x_833_ = lean_array_get(v___x_829_, v_cs_827_, v_j_831_);
lean_dec(v_j_831_);
lean_dec_ref(v_cs_827_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_shift_left(v___x_834_, v_x_823_);
v___x_836_ = lean_usize_sub(v___x_835_, v___x_834_);
v___x_837_ = lean_usize_land(v_x_822_, v___x_836_);
v___x_838_ = ((size_t)5ULL);
v___x_839_ = lean_usize_sub(v_x_823_, v___x_838_);
v___x_840_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_819_, v_f_820_, v___x_833_, v___x_837_, v___x_839_, v_x_824_);
v___x_841_ = lean_apply_4(v_toBind_826_, lean_box(0), lean_box(0), v___x_840_, v___f_832_);
return v___x_841_;
}
else
{
lean_object* v_toApplicative_842_; lean_object* v_vs_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_toApplicative_842_ = lean_ctor_get(v_inst_819_, 0);
v_vs_843_ = lean_ctor_get(v_x_821_, 0);
lean_inc_ref(v_vs_843_);
lean_dec_ref(v_x_821_);
v___x_844_ = lean_usize_to_nat(v_x_822_);
v___x_845_ = lean_array_get_size(v_vs_843_);
v___x_846_ = lean_nat_dec_lt(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v_toPure_847_; lean_object* v___x_848_; 
lean_inc_ref(v_toApplicative_842_);
lean_dec(v___x_844_);
lean_dec_ref(v_vs_843_);
lean_dec(v_f_820_);
lean_dec_ref(v_inst_819_);
v_toPure_847_ = lean_ctor_get(v_toApplicative_842_, 1);
lean_inc(v_toPure_847_);
lean_dec_ref(v_toApplicative_842_);
v___x_848_ = lean_apply_2(v_toPure_847_, lean_box(0), v_x_824_);
return v___x_848_;
}
else
{
uint8_t v___x_849_; 
v___x_849_ = lean_nat_dec_le(v___x_845_, v___x_845_);
if (v___x_849_ == 0)
{
if (v___x_846_ == 0)
{
lean_object* v_toPure_850_; lean_object* v___x_851_; 
lean_inc_ref(v_toApplicative_842_);
lean_dec(v___x_844_);
lean_dec_ref(v_vs_843_);
lean_dec(v_f_820_);
lean_dec_ref(v_inst_819_);
v_toPure_850_ = lean_ctor_get(v_toApplicative_842_, 1);
lean_inc(v_toPure_850_);
lean_dec_ref(v_toApplicative_842_);
v___x_851_ = lean_apply_2(v_toPure_850_, lean_box(0), v_x_824_);
return v___x_851_;
}
else
{
size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_usize_of_nat(v___x_844_);
lean_dec(v___x_844_);
v___x_853_ = lean_usize_of_nat(v___x_845_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_819_, v_f_820_, v_vs_843_, v___x_852_, v___x_853_, v_x_824_);
return v___x_854_;
}
}
else
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_usize_of_nat(v___x_844_);
lean_dec(v___x_844_);
v___x_856_ = lean_usize_of_nat(v___x_845_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_819_, v_f_820_, v_vs_843_, v___x_855_, v___x_856_, v_x_824_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_858_, lean_object* v_f_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
size_t v_x_215__boxed_864_; size_t v_x_216__boxed_865_; lean_object* v_res_866_; 
v_x_215__boxed_864_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_x_216__boxed_865_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_866_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_858_, v_f_859_, v_x_860_, v_x_215__boxed_864_, v_x_216__boxed_865_, v_x_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_867_, lean_object* v_m_868_, lean_object* v_inst_869_, lean_object* v_00_u03b2_870_, lean_object* v_f_871_, lean_object* v_x_872_, size_t v_x_873_, size_t v_x_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_869_, v_f_871_, v_x_872_, v_x_873_, v_x_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_877_, lean_object* v_m_878_, lean_object* v_inst_879_, lean_object* v_00_u03b2_880_, lean_object* v_f_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
size_t v_x_284__boxed_886_; size_t v_x_285__boxed_887_; lean_object* v_res_888_; 
v_x_284__boxed_886_ = lean_unbox_usize(v_x_883_);
lean_dec(v_x_883_);
v_x_285__boxed_887_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_res_888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_877_, v_m_878_, v_inst_879_, v_00_u03b2_880_, v_f_881_, v_x_882_, v_x_284__boxed_886_, v_x_285__boxed_887_, v_x_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_tail_889_, lean_object* v___x_890_, lean_object* v_toApplicative_891_, lean_object* v_inst_892_, lean_object* v_f_893_, lean_object* v_b_894_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_array_get_size(v_tail_889_);
v___x_896_ = lean_nat_dec_lt(v___x_890_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v_toPure_897_; lean_object* v___x_898_; 
lean_dec(v_f_893_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_tail_889_);
v_toPure_897_ = lean_ctor_get(v_toApplicative_891_, 1);
lean_inc(v_toPure_897_);
lean_dec_ref(v_toApplicative_891_);
v___x_898_ = lean_apply_2(v_toPure_897_, lean_box(0), v_b_894_);
return v___x_898_;
}
else
{
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_le(v___x_895_, v___x_895_);
if (v___x_899_ == 0)
{
if (v___x_896_ == 0)
{
lean_object* v_toPure_900_; lean_object* v___x_901_; 
lean_dec(v_f_893_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_tail_889_);
v_toPure_900_ = lean_ctor_get(v_toApplicative_891_, 1);
lean_inc(v_toPure_900_);
lean_dec_ref(v_toApplicative_891_);
v___x_901_ = lean_apply_2(v_toPure_900_, lean_box(0), v_b_894_);
return v___x_901_;
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
lean_dec_ref(v_toApplicative_891_);
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_of_nat(v___x_895_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_892_, v_f_893_, v_tail_889_, v___x_902_, v___x_903_, v_b_894_);
return v___x_904_;
}
}
else
{
size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v_toApplicative_891_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = lean_usize_of_nat(v___x_895_);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_892_, v_f_893_, v_tail_889_, v___x_905_, v___x_906_, v_b_894_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_tail_908_, lean_object* v___x_909_, lean_object* v_toApplicative_910_, lean_object* v_inst_911_, lean_object* v_f_912_, lean_object* v_b_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_tail_908_, v___x_909_, v_toApplicative_910_, v_inst_911_, v_f_912_, v_b_913_);
lean_dec(v___x_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_915_, lean_object* v_t_916_, lean_object* v_f_917_, lean_object* v_init_918_, lean_object* v_start_919_){
_start:
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_nat_dec_eq(v_start_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v_root_922_; lean_object* v_tail_923_; size_t v_shift_924_; lean_object* v_tailOff_925_; uint8_t v___x_926_; 
v_root_922_ = lean_ctor_get(v_t_916_, 0);
lean_inc_ref(v_root_922_);
v_tail_923_ = lean_ctor_get(v_t_916_, 1);
lean_inc_ref(v_tail_923_);
v_shift_924_ = lean_ctor_get_usize(v_t_916_, 4);
v_tailOff_925_ = lean_ctor_get(v_t_916_, 3);
lean_inc(v_tailOff_925_);
lean_dec_ref(v_t_916_);
v___x_926_ = lean_nat_dec_le(v_tailOff_925_, v_start_919_);
if (v___x_926_ == 0)
{
lean_object* v_toApplicative_927_; lean_object* v_toBind_928_; lean_object* v___f_929_; size_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_tailOff_925_);
v_toApplicative_927_ = lean_ctor_get(v_inst_915_, 0);
v_toBind_928_ = lean_ctor_get(v_inst_915_, 1);
lean_inc(v_toBind_928_);
lean_inc(v_f_917_);
lean_inc_ref(v_inst_915_);
lean_inc_ref(v_toApplicative_927_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_929_, 0, v_tail_923_);
lean_closure_set(v___f_929_, 1, v___x_920_);
lean_closure_set(v___f_929_, 2, v_toApplicative_927_);
lean_closure_set(v___f_929_, 3, v_inst_915_);
lean_closure_set(v___f_929_, 4, v_f_917_);
v___x_930_ = lean_usize_of_nat(v_start_919_);
v___x_931_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_915_, v_f_917_, v_root_922_, v___x_930_, v_shift_924_, v_init_918_);
v___x_932_ = lean_apply_4(v_toBind_928_, lean_box(0), lean_box(0), v___x_931_, v___f_929_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
lean_dec_ref(v_root_922_);
v___x_933_ = lean_nat_sub(v_start_919_, v_tailOff_925_);
lean_dec(v_tailOff_925_);
v___x_934_ = lean_array_get_size(v_tail_923_);
v___x_935_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v_toApplicative_936_; lean_object* v_toPure_937_; lean_object* v___x_938_; 
lean_dec(v___x_933_);
lean_dec_ref(v_tail_923_);
lean_dec(v_f_917_);
v_toApplicative_936_ = lean_ctor_get(v_inst_915_, 0);
lean_inc_ref(v_toApplicative_936_);
lean_dec_ref(v_inst_915_);
v_toPure_937_ = lean_ctor_get(v_toApplicative_936_, 1);
lean_inc(v_toPure_937_);
lean_dec_ref(v_toApplicative_936_);
v___x_938_ = lean_apply_2(v_toPure_937_, lean_box(0), v_init_918_);
return v___x_938_;
}
else
{
uint8_t v___x_939_; 
v___x_939_ = lean_nat_dec_le(v___x_934_, v___x_934_);
if (v___x_939_ == 0)
{
if (v___x_935_ == 0)
{
lean_object* v_toApplicative_940_; lean_object* v_toPure_941_; lean_object* v___x_942_; 
lean_dec(v___x_933_);
lean_dec_ref(v_tail_923_);
lean_dec(v_f_917_);
v_toApplicative_940_ = lean_ctor_get(v_inst_915_, 0);
lean_inc_ref(v_toApplicative_940_);
lean_dec_ref(v_inst_915_);
v_toPure_941_ = lean_ctor_get(v_toApplicative_940_, 1);
lean_inc(v_toPure_941_);
lean_dec_ref(v_toApplicative_940_);
v___x_942_ = lean_apply_2(v_toPure_941_, lean_box(0), v_init_918_);
return v___x_942_;
}
else
{
size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_usize_of_nat(v___x_933_);
lean_dec(v___x_933_);
v___x_944_ = lean_usize_of_nat(v___x_934_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_915_, v_f_917_, v_tail_923_, v___x_943_, v___x_944_, v_init_918_);
return v___x_945_;
}
}
else
{
size_t v___x_946_; size_t v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_usize_of_nat(v___x_933_);
lean_dec(v___x_933_);
v___x_947_ = lean_usize_of_nat(v___x_934_);
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_915_, v_f_917_, v_tail_923_, v___x_946_, v___x_947_, v_init_918_);
return v___x_948_;
}
}
}
}
else
{
lean_object* v_toApplicative_949_; lean_object* v_toBind_950_; lean_object* v_root_951_; lean_object* v_tail_952_; lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_toApplicative_949_ = lean_ctor_get(v_inst_915_, 0);
v_toBind_950_ = lean_ctor_get(v_inst_915_, 1);
lean_inc(v_toBind_950_);
v_root_951_ = lean_ctor_get(v_t_916_, 0);
lean_inc_ref(v_root_951_);
v_tail_952_ = lean_ctor_get(v_t_916_, 1);
lean_inc_ref(v_tail_952_);
lean_dec_ref(v_t_916_);
lean_inc(v_f_917_);
lean_inc_ref(v_inst_915_);
lean_inc_ref(v_toApplicative_949_);
v___f_953_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_953_, 0, v_tail_952_);
lean_closure_set(v___f_953_, 1, v___x_920_);
lean_closure_set(v___f_953_, 2, v_toApplicative_949_);
lean_closure_set(v___f_953_, 3, v_inst_915_);
lean_closure_set(v___f_953_, 4, v_f_917_);
v___x_954_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_915_, v_f_917_, v_root_951_, v_init_918_);
v___x_955_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_954_, v___f_953_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_956_, lean_object* v_t_957_, lean_object* v_f_958_, lean_object* v_init_959_, lean_object* v_start_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_956_, v_t_957_, v_f_958_, v_init_959_, v_start_960_);
lean_dec(v_start_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_962_, lean_object* v_m_963_, lean_object* v_inst_964_, lean_object* v_00_u03b2_965_, lean_object* v_t_966_, lean_object* v_f_967_, lean_object* v_init_968_, lean_object* v_start_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_964_, v_t_966_, v_f_967_, v_init_968_, v_start_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_971_, lean_object* v_m_972_, lean_object* v_inst_973_, lean_object* v_00_u03b2_974_, lean_object* v_t_975_, lean_object* v_f_976_, lean_object* v_init_977_, lean_object* v_start_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_971_, v_m_972_, v_inst_973_, v_00_u03b2_974_, v_t_975_, v_f_976_, v_init_977_, v_start_978_);
lean_dec(v_start_978_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_980_, lean_object* v_f_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
lean_object* v_cs_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_cs_984_ = lean_ctor_get(v_x_982_, 0);
lean_inc_ref(v_cs_984_);
lean_dec_ref(v_x_982_);
v___x_985_ = lean_array_get_size(v_cs_984_);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_nat_dec_lt(v___x_986_, v___x_985_);
if (v___x_987_ == 0)
{
lean_object* v_toApplicative_988_; lean_object* v_toPure_989_; lean_object* v___x_990_; 
lean_dec_ref(v_cs_984_);
lean_dec(v_f_981_);
v_toApplicative_988_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_988_);
lean_dec_ref(v_inst_980_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_988_, 1);
lean_inc(v_toPure_989_);
lean_dec_ref(v_toApplicative_988_);
v___x_990_ = lean_apply_2(v_toPure_989_, lean_box(0), v_x_983_);
return v___x_990_;
}
else
{
lean_object* v___f_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
lean_inc_ref(v_inst_980_);
v___f_991_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_991_, 0, v_inst_980_);
lean_closure_set(v___f_991_, 1, v_f_981_);
v___x_992_ = lean_usize_of_nat(v___x_985_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_980_, v___f_991_, v_cs_984_, v___x_992_, v___x_993_, v_x_983_);
return v___x_994_;
}
}
else
{
lean_object* v_vs_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_vs_995_ = lean_ctor_get(v_x_982_, 0);
lean_inc_ref(v_vs_995_);
lean_dec_ref(v_x_982_);
v___x_996_ = lean_array_get_size(v_vs_995_);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_nat_dec_lt(v___x_997_, v___x_996_);
if (v___x_998_ == 0)
{
lean_object* v_toApplicative_999_; lean_object* v_toPure_1000_; lean_object* v___x_1001_; 
lean_dec_ref(v_vs_995_);
lean_dec(v_f_981_);
v_toApplicative_999_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_999_);
lean_dec_ref(v_inst_980_);
v_toPure_1000_ = lean_ctor_get(v_toApplicative_999_, 1);
lean_inc(v_toPure_1000_);
lean_dec_ref(v_toApplicative_999_);
v___x_1001_ = lean_apply_2(v_toPure_1000_, lean_box(0), v_x_983_);
return v___x_1001_;
}
else
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_usize_of_nat(v___x_996_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_980_, v_f_981_, v_vs_995_, v___x_1002_, v___x_1003_, v_x_983_);
return v___x_1004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_1005_, lean_object* v_f_1006_, lean_object* v_c_1007_, lean_object* v_b_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1005_, v_f_1006_, v_c_1007_, v_b_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_1010_, lean_object* v_m_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_, lean_object* v_f_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1013_, v_f_1014_, v_x_1015_, v_x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_1018_, lean_object* v_f_1019_, lean_object* v_root_1020_, lean_object* v_____do__lift_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1018_, v_f_1019_, v_root_1020_, v_____do__lift_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1023_, lean_object* v_t_1024_, lean_object* v_f_1025_, lean_object* v_init_1026_){
_start:
{
lean_object* v_toApplicative_1027_; lean_object* v_toBind_1028_; lean_object* v_root_1029_; lean_object* v_tail_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_toApplicative_1027_ = lean_ctor_get(v_inst_1023_, 0);
v_toBind_1028_ = lean_ctor_get(v_inst_1023_, 1);
lean_inc(v_toBind_1028_);
v_root_1029_ = lean_ctor_get(v_t_1024_, 0);
lean_inc_ref(v_root_1029_);
v_tail_1030_ = lean_ctor_get(v_t_1024_, 1);
lean_inc_ref(v_tail_1030_);
lean_dec_ref(v_t_1024_);
lean_inc(v_f_1025_);
lean_inc_ref(v_inst_1023_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1031_, 0, v_inst_1023_);
lean_closure_set(v___f_1031_, 1, v_f_1025_);
lean_closure_set(v___f_1031_, 2, v_root_1029_);
v___x_1032_ = lean_array_get_size(v_tail_1030_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_nat_dec_lt(v___x_1033_, v___x_1032_);
if (v___x_1034_ == 0)
{
lean_object* v_toPure_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_inc_ref(v_toApplicative_1027_);
lean_dec_ref(v_tail_1030_);
lean_dec(v_f_1025_);
lean_dec_ref(v_inst_1023_);
v_toPure_1035_ = lean_ctor_get(v_toApplicative_1027_, 1);
lean_inc(v_toPure_1035_);
lean_dec_ref(v_toApplicative_1027_);
v___x_1036_ = lean_apply_2(v_toPure_1035_, lean_box(0), v_init_1026_);
v___x_1037_ = lean_apply_4(v_toBind_1028_, lean_box(0), lean_box(0), v___x_1036_, v___f_1031_);
return v___x_1037_;
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1038_ = lean_usize_of_nat(v___x_1032_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1023_, v_f_1025_, v_tail_1030_, v___x_1038_, v___x_1039_, v_init_1026_);
v___x_1041_ = lean_apply_4(v_toBind_1028_, lean_box(0), lean_box(0), v___x_1040_, v___f_1031_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1042_, lean_object* v_m_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_inst_1045_, lean_object* v_t_1046_, lean_object* v_f_1047_, lean_object* v_init_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1045_, v_t_1046_, v_f_1047_, v_init_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1050_, lean_object* v_____s_1051_){
_start:
{
lean_object* v_fst_1052_; 
v_fst_1052_ = lean_ctor_get(v_____s_1051_, 0);
if (lean_obj_tag(v_fst_1052_) == 0)
{
lean_object* v_snd_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_snd_1053_ = lean_ctor_get(v_____s_1051_, 1);
lean_inc(v_snd_1053_);
lean_dec_ref(v_____s_1051_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_snd_1053_);
v___x_1055_ = lean_apply_2(v_toPure_1050_, lean_box(0), v___x_1054_);
return v___x_1055_;
}
else
{
lean_object* v_val_1056_; lean_object* v___x_1057_; 
lean_inc_ref(v_fst_1052_);
lean_dec_ref(v_____s_1051_);
v_val_1056_ = lean_ctor_get(v_fst_1052_, 0);
lean_inc(v_val_1056_);
lean_dec_ref(v_fst_1052_);
v___x_1057_ = lean_apply_2(v_toPure_1050_, lean_box(0), v_val_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1058_, lean_object* v_toPure_1059_, lean_object* v___x_1060_, lean_object* v_____do__lift_1061_){
_start:
{
if (lean_obj_tag(v_____do__lift_1061_) == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_____do__lift_1061_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_snd_1058_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = lean_apply_2(v_toPure_1059_, lean_box(0), v___x_1064_);
return v___x_1065_;
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_snd_1058_);
v_a_1066_ = lean_ctor_get(v_____do__lift_1061_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_____do__lift_1061_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1068_ = v_____do__lift_1061_;
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v_____do__lift_1061_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1060_);
lean_ctor_set(v___x_1070_, 1, v_a_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_apply_2(v_toPure_1059_, lean_box(0), v___x_1072_);
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1076_, lean_object* v___x_1077_, lean_object* v_f_1078_, lean_object* v_toBind_1079_, lean_object* v_a_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_snd_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_snd_1083_ = lean_ctor_get(v___y_1082_, 1);
lean_inc_n(v_snd_1083_, 2);
lean_dec_ref(v___y_1082_);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1084_, 0, v_snd_1083_);
lean_closure_set(v___f_1084_, 1, v_toPure_1076_);
lean_closure_set(v___f_1084_, 2, v___x_1077_);
v___x_1085_ = lean_apply_2(v_f_1078_, v_a_1080_, v_snd_1083_);
v___x_1086_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v___x_1085_, v___f_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1087_, lean_object* v_f_1088_, lean_object* v_n_1089_, lean_object* v_b_1090_){
_start:
{
if (lean_obj_tag(v_n_1089_) == 0)
{
lean_object* v_toApplicative_1091_; lean_object* v_toBind_1092_; lean_object* v_toPure_1093_; lean_object* v_cs_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; size_t v_sz_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_toApplicative_1091_ = lean_ctor_get(v_inst_1087_, 0);
v_toBind_1092_ = lean_ctor_get(v_inst_1087_, 1);
lean_inc_n(v_toBind_1092_, 2);
v_toPure_1093_ = lean_ctor_get(v_toApplicative_1091_, 1);
v_cs_1094_ = lean_ctor_get(v_n_1089_, 0);
lean_inc_ref(v_cs_1094_);
lean_dec_ref(v_n_1089_);
lean_inc_n(v_toPure_1093_, 2);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1095_, 0, v_toPure_1093_);
v___x_1096_ = lean_box(0);
lean_inc_ref(v_inst_1087_);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2), 8, 5);
lean_closure_set(v___f_1097_, 0, v_toPure_1093_);
lean_closure_set(v___f_1097_, 1, v___x_1096_);
lean_closure_set(v___f_1097_, 2, v_inst_1087_);
lean_closure_set(v___f_1097_, 3, v_f_1088_);
lean_closure_set(v___f_1097_, 4, v_toBind_1092_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v_b_1090_);
v_sz_1099_ = lean_array_size(v_cs_1094_);
v___x_1100_ = ((size_t)0ULL);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1087_, v_cs_1094_, v___f_1097_, v_sz_1099_, v___x_1100_, v___x_1098_);
v___x_1102_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1101_, v___f_1095_);
return v___x_1102_;
}
else
{
lean_object* v_toApplicative_1103_; lean_object* v_toBind_1104_; lean_object* v_toPure_1105_; lean_object* v_vs_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_toApplicative_1103_ = lean_ctor_get(v_inst_1087_, 0);
v_toBind_1104_ = lean_ctor_get(v_inst_1087_, 1);
lean_inc_n(v_toBind_1104_, 2);
v_toPure_1105_ = lean_ctor_get(v_toApplicative_1103_, 1);
v_vs_1106_ = lean_ctor_get(v_n_1089_, 0);
lean_inc_ref(v_vs_1106_);
lean_dec_ref(v_n_1089_);
lean_inc_n(v_toPure_1105_, 2);
v___f_1107_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1107_, 0, v_toPure_1105_);
v___x_1108_ = lean_box(0);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1109_, 0, v_toPure_1105_);
lean_closure_set(v___f_1109_, 1, v___x_1108_);
lean_closure_set(v___f_1109_, 2, v_f_1088_);
lean_closure_set(v___f_1109_, 3, v_toBind_1104_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v_b_1090_);
v_sz_1111_ = lean_array_size(v_vs_1106_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1087_, v_vs_1106_, v___f_1109_, v_sz_1111_, v___x_1112_, v___x_1110_);
v___x_1114_ = lean_apply_4(v_toBind_1104_, lean_box(0), lean_box(0), v___x_1113_, v___f_1107_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1115_, lean_object* v___x_1116_, lean_object* v_inst_1117_, lean_object* v_f_1118_, lean_object* v_toBind_1119_, lean_object* v_a_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_snd_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_snd_1123_ = lean_ctor_get(v___y_1122_, 1);
lean_inc_n(v_snd_1123_, 2);
lean_dec_ref(v___y_1122_);
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1124_, 0, v_snd_1123_);
lean_closure_set(v___f_1124_, 1, v_toPure_1115_);
lean_closure_set(v___f_1124_, 2, v___x_1116_);
v___x_1125_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1117_, v_f_1118_, v_a_1120_, v_snd_1123_);
v___x_1126_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1125_, v___f_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_m_1129_, lean_object* v_inst_1130_, lean_object* v_inh_1131_, lean_object* v_f_1132_, lean_object* v_n_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1130_, v_f_1132_, v_n_1133_, v_b_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_m_1138_, lean_object* v_inst_1139_, lean_object* v_inh_1140_, lean_object* v_f_1141_, lean_object* v_n_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1136_, v_00_u03b2_1137_, v_m_1138_, v_inst_1139_, v_inh_1140_, v_f_1141_, v_n_1142_, v_b_1143_);
lean_dec(v_inh_1140_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1145_, lean_object* v_____s_1146_){
_start:
{
lean_object* v_fst_1147_; 
v_fst_1147_ = lean_ctor_get(v_____s_1146_, 0);
if (lean_obj_tag(v_fst_1147_) == 0)
{
lean_object* v_snd_1148_; lean_object* v___x_1149_; 
v_snd_1148_ = lean_ctor_get(v_____s_1146_, 1);
lean_inc(v_snd_1148_);
lean_dec_ref(v_____s_1146_);
v___x_1149_ = lean_apply_2(v_toPure_1145_, lean_box(0), v_snd_1148_);
return v___x_1149_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1151_; 
lean_inc_ref(v_fst_1147_);
lean_dec_ref(v_____s_1146_);
v_val_1150_ = lean_ctor_get(v_fst_1147_, 0);
lean_inc(v_val_1150_);
lean_dec_ref(v_fst_1147_);
v___x_1151_ = lean_apply_2(v_toPure_1145_, lean_box(0), v_val_1150_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1152_, lean_object* v_toPure_1153_, lean_object* v___x_1154_, lean_object* v_____do__lift_1155_){
_start:
{
if (lean_obj_tag(v_____do__lift_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v___x_1154_);
v_a_1156_ = lean_ctor_get(v_____do__lift_1155_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_____do__lift_1155_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1158_ = v_____do__lift_1155_;
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v_____do__lift_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_a_1156_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_snd_1152_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1161_);
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_apply_2(v_toPure_1153_, lean_box(0), v___x_1163_);
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_snd_1152_);
v_a_1167_ = lean_ctor_get(v_____do__lift_1155_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_____do__lift_1155_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v_____do__lift_1155_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v_____do__lift_1155_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1154_);
lean_ctor_set(v___x_1171_, 1, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_apply_2(v_toPure_1153_, lean_box(0), v___x_1173_);
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1177_, lean_object* v___x_1178_, lean_object* v_f_1179_, lean_object* v_toBind_1180_, lean_object* v_a_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_snd_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_snd_1184_ = lean_ctor_get(v___y_1183_, 1);
lean_inc_n(v_snd_1184_, 2);
lean_dec_ref(v___y_1183_);
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1185_, 0, v_snd_1184_);
lean_closure_set(v___f_1185_, 1, v_toPure_1177_);
lean_closure_set(v___f_1185_, 2, v___x_1178_);
v___x_1186_ = lean_apply_2(v_f_1179_, v_a_1181_, v_snd_1184_);
v___x_1187_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1186_, v___f_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1188_, lean_object* v_f_1189_, lean_object* v_toBind_1190_, lean_object* v_tail_1191_, lean_object* v_inst_1192_, lean_object* v___f_1193_, lean_object* v_____do__lift_1194_){
_start:
{
if (lean_obj_tag(v_____do__lift_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
lean_dec(v___f_1193_);
lean_dec_ref(v_inst_1192_);
lean_dec_ref(v_tail_1191_);
lean_dec(v_toBind_1190_);
lean_dec(v_f_1189_);
v_a_1195_ = lean_ctor_get(v_____do__lift_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v_____do__lift_1194_);
v___x_1196_ = lean_apply_2(v_toPure_1188_, lean_box(0), v_a_1195_);
return v___x_1196_;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; size_t v_sz_1201_; size_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1197_ = lean_ctor_get(v_____do__lift_1194_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v_____do__lift_1194_);
v___x_1198_ = lean_box(0);
lean_inc(v_toBind_1190_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1199_, 0, v_toPure_1188_);
lean_closure_set(v___f_1199_, 1, v___x_1198_);
lean_closure_set(v___f_1199_, 2, v_f_1189_);
lean_closure_set(v___f_1199_, 3, v_toBind_1190_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v_a_1197_);
v_sz_1201_ = lean_array_size(v_tail_1191_);
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1192_, v_tail_1191_, v___f_1199_, v_sz_1201_, v___x_1202_, v___x_1200_);
v___x_1204_ = lean_apply_4(v_toBind_1190_, lean_box(0), lean_box(0), v___x_1203_, v___f_1193_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1205_, lean_object* v_t_1206_, lean_object* v_init_1207_, lean_object* v_f_1208_){
_start:
{
lean_object* v_toApplicative_1209_; lean_object* v_toBind_1210_; lean_object* v_root_1211_; lean_object* v_tail_1212_; lean_object* v_toPure_1213_; lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; 
v_toApplicative_1209_ = lean_ctor_get(v_inst_1205_, 0);
v_toBind_1210_ = lean_ctor_get(v_inst_1205_, 1);
lean_inc_n(v_toBind_1210_, 2);
v_root_1211_ = lean_ctor_get(v_t_1206_, 0);
lean_inc_ref(v_root_1211_);
v_tail_1212_ = lean_ctor_get(v_t_1206_, 1);
lean_inc_ref(v_tail_1212_);
lean_dec_ref(v_t_1206_);
v_toPure_1213_ = lean_ctor_get(v_toApplicative_1209_, 1);
lean_inc_n(v_toPure_1213_, 2);
lean_inc(v_f_1208_);
lean_inc_ref(v_inst_1205_);
v___x_1214_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1205_, v_f_1208_, v_root_1211_, v_init_1207_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1215_, 0, v_toPure_1213_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1216_, 0, v_toPure_1213_);
lean_closure_set(v___f_1216_, 1, v_f_1208_);
lean_closure_set(v___f_1216_, 2, v_toBind_1210_);
lean_closure_set(v___f_1216_, 3, v_tail_1212_);
lean_closure_set(v___f_1216_, 4, v_inst_1205_);
lean_closure_set(v___f_1216_, 5, v___f_1215_);
v___x_1217_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1214_, v___f_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1218_, lean_object* v_m_1219_, lean_object* v_inst_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_t_1222_, lean_object* v_init_1223_, lean_object* v_f_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1220_, v_t_1222_, v_init_1223_, v_f_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn), 7, 3);
lean_closure_set(v___x_1227_, 0, lean_box(0));
lean_closure_set(v___x_1227_, 1, lean_box(0));
lean_closure_set(v___x_1227_, 2, v_inst_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1228_, lean_object* v_m_1229_, lean_object* v_inst_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn), 7, 3);
lean_closure_set(v___x_1231_, 0, lean_box(0));
lean_closure_set(v___x_1231_, 1, lean_box(0));
lean_closure_set(v___x_1231_, 2, v_inst_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1232_, lean_object* v_____s_1233_){
_start:
{
lean_object* v_fst_1234_; 
v_fst_1234_ = lean_ctor_get(v_____s_1233_, 0);
lean_inc(v_fst_1234_);
lean_dec_ref(v_____s_1233_);
if (lean_obj_tag(v_fst_1234_) == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1235_);
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1238_; 
v_val_1237_ = lean_ctor_get(v_fst_1234_, 0);
lean_inc(v_val_1237_);
lean_dec_ref(v_fst_1234_);
v___x_1238_ = lean_apply_2(v_toPure_1232_, lean_box(0), v_val_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1239_, lean_object* v_toPure_1240_, lean_object* v___x_1241_, lean_object* v_____do__lift_1242_){
_start:
{
if (lean_obj_tag(v_____do__lift_1242_) == 1)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_____do__lift_1242_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1239_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
v___x_1246_ = lean_apply_2(v_toPure_1240_, lean_box(0), v___x_1245_);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v_____do__lift_1242_);
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1241_);
v___x_1248_ = lean_apply_2(v_toPure_1240_, lean_box(0), v___x_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1249_, lean_object* v_toBind_1250_, lean_object* v___f_1251_, lean_object* v_a_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_apply_1(v_f_1249_, v_a_1252_);
v___x_1256_ = lean_apply_4(v_toBind_1250_, lean_box(0), lean_box(0), v___x_1255_, v___f_1251_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1257_, lean_object* v_toBind_1258_, lean_object* v___f_1259_, lean_object* v_a_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1257_, v_toBind_1258_, v___f_1259_, v_a_1260_, v_x_1261_, v___y_1262_);
lean_dec_ref(v___y_1262_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1267_, lean_object* v_f_1268_, lean_object* v_toBind_1269_, lean_object* v___f_1270_, lean_object* v_a_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1267_, v_f_1268_, v_toBind_1269_, v___f_1270_, v_a_1271_, v_x_1272_, v___y_1273_);
lean_dec_ref(v___y_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1275_, lean_object* v_f_1276_, lean_object* v_x_1277_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 0)
{
lean_object* v_toApplicative_1278_; lean_object* v_cs_1279_; lean_object* v_toBind_1280_; lean_object* v_toPure_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; size_t v_sz_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_toApplicative_1278_ = lean_ctor_get(v_inst_1275_, 0);
v_cs_1279_ = lean_ctor_get(v_x_1277_, 0);
lean_inc_ref(v_cs_1279_);
lean_dec_ref(v_x_1277_);
v_toBind_1280_ = lean_ctor_get(v_inst_1275_, 1);
lean_inc_n(v_toBind_1280_, 2);
v_toPure_1281_ = lean_ctor_get(v_toApplicative_1278_, 1);
v___x_1282_ = lean_box(0);
v___x_1283_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1281_, 2);
v___f_1284_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1284_, 0, v_toPure_1281_);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1285_, 0, v___x_1282_);
lean_closure_set(v___f_1285_, 1, v_toPure_1281_);
lean_closure_set(v___f_1285_, 2, v___x_1283_);
lean_inc_ref(v_inst_1275_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1286_, 0, v_inst_1275_);
lean_closure_set(v___f_1286_, 1, v_f_1276_);
lean_closure_set(v___f_1286_, 2, v_toBind_1280_);
lean_closure_set(v___f_1286_, 3, v___f_1285_);
v_sz_1287_ = lean_array_size(v_cs_1279_);
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1275_, v_cs_1279_, v___f_1286_, v_sz_1287_, v___x_1288_, v___x_1283_);
v___x_1290_ = lean_apply_4(v_toBind_1280_, lean_box(0), lean_box(0), v___x_1289_, v___f_1284_);
return v___x_1290_;
}
else
{
lean_object* v_toApplicative_1291_; lean_object* v_vs_1292_; lean_object* v_toBind_1293_; lean_object* v_toPure_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; size_t v_sz_1300_; size_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_toApplicative_1291_ = lean_ctor_get(v_inst_1275_, 0);
v_vs_1292_ = lean_ctor_get(v_x_1277_, 0);
lean_inc_ref(v_vs_1292_);
lean_dec_ref(v_x_1277_);
v_toBind_1293_ = lean_ctor_get(v_inst_1275_, 1);
lean_inc_n(v_toBind_1293_, 2);
v_toPure_1294_ = lean_ctor_get(v_toApplicative_1291_, 1);
v___x_1295_ = lean_box(0);
v___x_1296_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1294_, 2);
v___f_1297_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1297_, 0, v_toPure_1294_);
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1298_, 0, v___x_1295_);
lean_closure_set(v___f_1298_, 1, v_toPure_1294_);
lean_closure_set(v___f_1298_, 2, v___x_1296_);
v___f_1299_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1299_, 0, v_f_1276_);
lean_closure_set(v___f_1299_, 1, v_toBind_1293_);
lean_closure_set(v___f_1299_, 2, v___f_1298_);
v_sz_1300_ = lean_array_size(v_vs_1292_);
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1275_, v_vs_1292_, v___f_1299_, v_sz_1300_, v___x_1301_, v___x_1296_);
v___x_1303_ = lean_apply_4(v_toBind_1293_, lean_box(0), lean_box(0), v___x_1302_, v___f_1297_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1304_, lean_object* v_f_1305_, lean_object* v_toBind_1306_, lean_object* v___f_1307_, lean_object* v_a_1308_, lean_object* v_x_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1304_, v_f_1305_, v_a_1308_);
v___x_1312_ = lean_apply_4(v_toBind_1306_, lean_box(0), lean_box(0), v___x_1311_, v___f_1307_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1313_, lean_object* v_m_1314_, lean_object* v_inst_1315_, lean_object* v_00_u03b2_1316_, lean_object* v_f_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1315_, v_f_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1320_, lean_object* v_____do__lift_1321_, lean_object* v_____s_1322_){
_start:
{
lean_object* v_fst_1323_; 
v_fst_1323_ = lean_ctor_get(v_____s_1322_, 0);
lean_inc(v_fst_1323_);
lean_dec_ref(v_____s_1322_);
if (lean_obj_tag(v_fst_1323_) == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_apply_2(v_toPure_1320_, lean_box(0), v_____do__lift_1321_);
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; lean_object* v___x_1326_; 
lean_dec(v_____do__lift_1321_);
v_val_1325_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_val_1325_);
lean_dec_ref(v_fst_1323_);
v___x_1326_ = lean_apply_2(v_toPure_1320_, lean_box(0), v_val_1325_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1327_, lean_object* v_toPure_1328_, lean_object* v___x_1329_, lean_object* v_____do__lift_1330_){
_start:
{
if (lean_obj_tag(v_____do__lift_1330_) == 1)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_____do__lift_1330_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1327_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
v___x_1334_ = lean_apply_2(v_toPure_1328_, lean_box(0), v___x_1333_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_____do__lift_1330_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1329_);
v___x_1336_ = lean_apply_2(v_toPure_1328_, lean_box(0), v___x_1335_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1337_, lean_object* v_toBind_1338_, lean_object* v___f_1339_, lean_object* v_a_1340_, lean_object* v_x_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_apply_1(v_f_1337_, v_a_1340_);
v___x_1344_ = lean_apply_4(v_toBind_1338_, lean_box(0), lean_box(0), v___x_1343_, v___f_1339_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1345_, lean_object* v_toBind_1346_, lean_object* v___f_1347_, lean_object* v_a_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1345_, v_toBind_1346_, v___f_1347_, v_a_1348_, v_x_1349_, v___y_1350_);
lean_dec_ref(v___y_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1352_, lean_object* v_f_1353_, lean_object* v_toBind_1354_, lean_object* v_tail_1355_, lean_object* v_inst_1356_, lean_object* v_____do__lift_1357_){
_start:
{
if (lean_obj_tag(v_____do__lift_1357_) == 0)
{
lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; size_t v_sz_1363_; size_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc(v_toPure_1352_);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1358_, 0, v_toPure_1352_);
lean_closure_set(v___f_1358_, 1, v_____do__lift_1357_);
v___x_1359_ = lean_box(0);
v___x_1360_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1361_, 0, v___x_1359_);
lean_closure_set(v___f_1361_, 1, v_toPure_1352_);
lean_closure_set(v___f_1361_, 2, v___x_1360_);
lean_inc(v_toBind_1354_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1362_, 0, v_f_1353_);
lean_closure_set(v___f_1362_, 1, v_toBind_1354_);
lean_closure_set(v___f_1362_, 2, v___f_1361_);
v_sz_1363_ = lean_array_size(v_tail_1355_);
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1356_, v_tail_1355_, v___f_1362_, v_sz_1363_, v___x_1364_, v___x_1360_);
v___x_1366_ = lean_apply_4(v_toBind_1354_, lean_box(0), lean_box(0), v___x_1365_, v___f_1358_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; 
lean_dec_ref(v_inst_1356_);
lean_dec_ref(v_tail_1355_);
lean_dec(v_toBind_1354_);
lean_dec(v_f_1353_);
v___x_1367_ = lean_apply_2(v_toPure_1352_, lean_box(0), v_____do__lift_1357_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1368_, lean_object* v_t_1369_, lean_object* v_f_1370_){
_start:
{
lean_object* v_toApplicative_1371_; lean_object* v_toBind_1372_; lean_object* v_root_1373_; lean_object* v_tail_1374_; lean_object* v_toPure_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; 
v_toApplicative_1371_ = lean_ctor_get(v_inst_1368_, 0);
v_toBind_1372_ = lean_ctor_get(v_inst_1368_, 1);
lean_inc_n(v_toBind_1372_, 2);
v_root_1373_ = lean_ctor_get(v_t_1369_, 0);
lean_inc_ref(v_root_1373_);
v_tail_1374_ = lean_ctor_get(v_t_1369_, 1);
lean_inc_ref(v_tail_1374_);
lean_dec_ref(v_t_1369_);
v_toPure_1375_ = lean_ctor_get(v_toApplicative_1371_, 1);
lean_inc(v_toPure_1375_);
lean_inc(v_f_1370_);
lean_inc_ref(v_inst_1368_);
v___x_1376_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1368_, v_f_1370_, v_root_1373_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1377_, 0, v_toPure_1375_);
lean_closure_set(v___f_1377_, 1, v_f_1370_);
lean_closure_set(v___f_1377_, 2, v_toBind_1372_);
lean_closure_set(v___f_1377_, 3, v_tail_1374_);
lean_closure_set(v___f_1377_, 4, v_inst_1368_);
v___x_1378_ = lean_apply_4(v_toBind_1372_, lean_box(0), lean_box(0), v___x_1376_, v___f_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1379_, lean_object* v_m_1380_, lean_object* v_inst_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_t_1383_, lean_object* v_f_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1381_, v_t_1383_, v_f_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1386_, lean_object* v_f_1387_, lean_object* v_x_1388_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v_cs_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_cs_1389_ = lean_ctor_get(v_x_1388_, 0);
lean_inc_ref(v_cs_1389_);
lean_dec_ref(v_x_1388_);
lean_inc_ref(v_inst_1386_);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1390_, 0, v_inst_1386_);
lean_closure_set(v___f_1390_, 1, v_f_1387_);
v___x_1391_ = lean_array_get_size(v_cs_1389_);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1386_, v___f_1390_, v_cs_1389_, v___x_1391_, lean_box(0));
return v___x_1392_;
}
else
{
lean_object* v_vs_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_vs_1393_ = lean_ctor_get(v_x_1388_, 0);
lean_inc_ref(v_vs_1393_);
lean_dec_ref(v_x_1388_);
v___x_1394_ = lean_array_get_size(v_vs_1393_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1386_, v_f_1387_, v_vs_1393_, v___x_1394_, lean_box(0));
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1396_, lean_object* v_f_1397_, lean_object* v_c_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1396_, v_f_1397_, v_c_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1400_, lean_object* v_m_1401_, lean_object* v_inst_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_f_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1402_, v_f_1404_, v_x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1407_, lean_object* v_f_1408_, lean_object* v_root_1409_, lean_object* v_toPure_1410_, lean_object* v_____do__lift_1411_){
_start:
{
if (lean_obj_tag(v_____do__lift_1411_) == 0)
{
lean_object* v___x_1412_; 
lean_dec(v_toPure_1410_);
v___x_1412_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1407_, v_f_1408_, v_root_1409_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
lean_dec_ref(v_root_1409_);
lean_dec(v_f_1408_);
lean_dec_ref(v_inst_1407_);
v___x_1413_ = lean_apply_2(v_toPure_1410_, lean_box(0), v_____do__lift_1411_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1414_, lean_object* v_t_1415_, lean_object* v_f_1416_){
_start:
{
lean_object* v_toApplicative_1417_; lean_object* v_toBind_1418_; lean_object* v_root_1419_; lean_object* v_tail_1420_; lean_object* v_toPure_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; 
v_toApplicative_1417_ = lean_ctor_get(v_inst_1414_, 0);
v_toBind_1418_ = lean_ctor_get(v_inst_1414_, 1);
lean_inc(v_toBind_1418_);
v_root_1419_ = lean_ctor_get(v_t_1415_, 0);
lean_inc_ref(v_root_1419_);
v_tail_1420_ = lean_ctor_get(v_t_1415_, 1);
lean_inc_ref(v_tail_1420_);
lean_dec_ref(v_t_1415_);
v_toPure_1421_ = lean_ctor_get(v_toApplicative_1417_, 1);
lean_inc(v_toPure_1421_);
v___x_1422_ = lean_array_get_size(v_tail_1420_);
lean_inc(v_f_1416_);
lean_inc_ref(v_inst_1414_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1414_, v_f_1416_, v_tail_1420_, v___x_1422_, lean_box(0));
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1424_, 0, v_inst_1414_);
lean_closure_set(v___f_1424_, 1, v_f_1416_);
lean_closure_set(v___f_1424_, 2, v_root_1419_);
lean_closure_set(v___f_1424_, 3, v_toPure_1421_);
v___x_1425_ = lean_apply_4(v_toBind_1418_, lean_box(0), lean_box(0), v___x_1423_, v___f_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1426_, lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_t_1430_, lean_object* v_f_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1428_, v_t_1430_, v_f_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_apply_1(v_f_1433_, v___y_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1437_, lean_object* v_f_1438_, lean_object* v_x_1439_){
_start:
{
if (lean_obj_tag(v_x_1439_) == 0)
{
lean_object* v_cs_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_cs_1440_ = lean_ctor_get(v_x_1439_, 0);
lean_inc_ref(v_cs_1440_);
lean_dec_ref(v_x_1439_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_array_get_size(v_cs_1440_);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_nat_dec_lt(v___x_1441_, v___x_1442_);
if (v___x_1444_ == 0)
{
lean_object* v_toApplicative_1445_; lean_object* v_toPure_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_cs_1440_);
lean_dec(v_f_1438_);
v_toApplicative_1445_ = lean_ctor_get(v_inst_1437_, 0);
lean_inc_ref(v_toApplicative_1445_);
lean_dec_ref(v_inst_1437_);
v_toPure_1446_ = lean_ctor_get(v_toApplicative_1445_, 1);
lean_inc(v_toPure_1446_);
lean_dec_ref(v_toApplicative_1445_);
v___x_1447_ = lean_apply_2(v_toPure_1446_, lean_box(0), v___x_1443_);
return v___x_1447_;
}
else
{
lean_object* v___f_1448_; uint8_t v___x_1449_; 
lean_inc_ref(v_inst_1437_);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1448_, 0, v_inst_1437_);
lean_closure_set(v___f_1448_, 1, v_f_1438_);
v___x_1449_ = lean_nat_dec_le(v___x_1442_, v___x_1442_);
if (v___x_1449_ == 0)
{
if (v___x_1444_ == 0)
{
lean_object* v_toApplicative_1450_; lean_object* v_toPure_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v___f_1448_);
lean_dec_ref(v_cs_1440_);
v_toApplicative_1450_ = lean_ctor_get(v_inst_1437_, 0);
lean_inc_ref(v_toApplicative_1450_);
lean_dec_ref(v_inst_1437_);
v_toPure_1451_ = lean_ctor_get(v_toApplicative_1450_, 1);
lean_inc(v_toPure_1451_);
lean_dec_ref(v_toApplicative_1450_);
v___x_1452_ = lean_apply_2(v_toPure_1451_, lean_box(0), v___x_1443_);
return v___x_1452_;
}
else
{
size_t v___x_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = ((size_t)0ULL);
v___x_1454_ = lean_usize_of_nat(v___x_1442_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1437_, v___f_1448_, v_cs_1440_, v___x_1453_, v___x_1454_, v___x_1443_);
return v___x_1455_;
}
}
else
{
size_t v___x_1456_; size_t v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = ((size_t)0ULL);
v___x_1457_ = lean_usize_of_nat(v___x_1442_);
v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1437_, v___f_1448_, v_cs_1440_, v___x_1456_, v___x_1457_, v___x_1443_);
return v___x_1458_;
}
}
}
else
{
lean_object* v_vs_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_vs_1459_ = lean_ctor_get(v_x_1439_, 0);
lean_inc_ref(v_vs_1459_);
lean_dec_ref(v_x_1439_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_array_get_size(v_vs_1459_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
if (v___x_1463_ == 0)
{
lean_object* v_toApplicative_1464_; lean_object* v_toPure_1465_; lean_object* v___x_1466_; 
lean_dec_ref(v_vs_1459_);
lean_dec(v_f_1438_);
v_toApplicative_1464_ = lean_ctor_get(v_inst_1437_, 0);
lean_inc_ref(v_toApplicative_1464_);
lean_dec_ref(v_inst_1437_);
v_toPure_1465_ = lean_ctor_get(v_toApplicative_1464_, 1);
lean_inc(v_toPure_1465_);
lean_dec_ref(v_toApplicative_1464_);
v___x_1466_ = lean_apply_2(v_toPure_1465_, lean_box(0), v___x_1462_);
return v___x_1466_;
}
else
{
lean_object* v___f_1467_; uint8_t v___x_1468_; 
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1467_, 0, v_f_1438_);
v___x_1468_ = lean_nat_dec_le(v___x_1461_, v___x_1461_);
if (v___x_1468_ == 0)
{
if (v___x_1463_ == 0)
{
lean_object* v_toApplicative_1469_; lean_object* v_toPure_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v___f_1467_);
lean_dec_ref(v_vs_1459_);
v_toApplicative_1469_ = lean_ctor_get(v_inst_1437_, 0);
lean_inc_ref(v_toApplicative_1469_);
lean_dec_ref(v_inst_1437_);
v_toPure_1470_ = lean_ctor_get(v_toApplicative_1469_, 1);
lean_inc(v_toPure_1470_);
lean_dec_ref(v_toApplicative_1469_);
v___x_1471_ = lean_apply_2(v_toPure_1470_, lean_box(0), v___x_1462_);
return v___x_1471_;
}
else
{
size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = ((size_t)0ULL);
v___x_1473_ = lean_usize_of_nat(v___x_1461_);
v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1437_, v___f_1467_, v_vs_1459_, v___x_1472_, v___x_1473_, v___x_1462_);
return v___x_1474_;
}
}
else
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = lean_usize_of_nat(v___x_1461_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1437_, v___f_1467_, v_vs_1459_, v___x_1475_, v___x_1476_, v___x_1462_);
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1478_, lean_object* v_f_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1478_, v_f_1479_, v___y_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1483_, lean_object* v_m_1484_, lean_object* v_inst_1485_, lean_object* v_f_1486_, lean_object* v_x_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1485_, v_f_1486_, v_x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1489_, lean_object* v_x_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_apply_1(v_f_1489_, v___y_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1493_, lean_object* v_toPure_1494_, lean_object* v_inst_1495_, lean_object* v___f_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_array_get_size(v_tail_1493_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_nat_dec_lt(v___x_1498_, v___x_1499_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec(v___f_1496_);
lean_dec_ref(v_inst_1495_);
lean_dec_ref(v_tail_1493_);
v___x_1502_ = lean_apply_2(v_toPure_1494_, lean_box(0), v___x_1500_);
return v___x_1502_;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_nat_dec_le(v___x_1499_, v___x_1499_);
if (v___x_1503_ == 0)
{
if (v___x_1501_ == 0)
{
lean_object* v___x_1504_; 
lean_dec(v___f_1496_);
lean_dec_ref(v_inst_1495_);
lean_dec_ref(v_tail_1493_);
v___x_1504_ = lean_apply_2(v_toPure_1494_, lean_box(0), v___x_1500_);
return v___x_1504_;
}
else
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_toPure_1494_);
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = lean_usize_of_nat(v___x_1499_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1495_, v___f_1496_, v_tail_1493_, v___x_1505_, v___x_1506_, v___x_1500_);
return v___x_1507_;
}
}
else
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
lean_dec(v_toPure_1494_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = lean_usize_of_nat(v___x_1499_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1495_, v___f_1496_, v_tail_1493_, v___x_1508_, v___x_1509_, v___x_1500_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1511_, lean_object* v_t_1512_, lean_object* v_f_1513_){
_start:
{
lean_object* v_toApplicative_1514_; lean_object* v_toPure_1515_; lean_object* v_toSeqRight_1516_; lean_object* v_root_1517_; lean_object* v_tail_1518_; lean_object* v___f_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_toApplicative_1514_ = lean_ctor_get(v_inst_1511_, 0);
v_toPure_1515_ = lean_ctor_get(v_toApplicative_1514_, 1);
v_toSeqRight_1516_ = lean_ctor_get(v_toApplicative_1514_, 4);
lean_inc(v_toSeqRight_1516_);
v_root_1517_ = lean_ctor_get(v_t_1512_, 0);
lean_inc_ref(v_root_1517_);
v_tail_1518_ = lean_ctor_get(v_t_1512_, 1);
lean_inc_ref(v_tail_1518_);
lean_dec_ref(v_t_1512_);
lean_inc(v_f_1513_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1519_, 0, v_f_1513_);
lean_inc_ref(v_inst_1511_);
lean_inc(v_toPure_1515_);
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1520_, 0, v_tail_1518_);
lean_closure_set(v___f_1520_, 1, v_toPure_1515_);
lean_closure_set(v___f_1520_, 2, v_inst_1511_);
lean_closure_set(v___f_1520_, 3, v___f_1519_);
v___x_1521_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1511_, v_f_1513_, v_root_1517_);
v___x_1522_ = lean_apply_4(v_toSeqRight_1516_, lean_box(0), lean_box(0), v___x_1521_, v___f_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1523_, lean_object* v_m_1524_, lean_object* v_inst_1525_, lean_object* v_t_1526_, lean_object* v_f_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1525_, v_t_1526_, v_f_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_j_1529_, lean_object* v_cs_1530_, lean_object* v_toApplicative_1531_, lean_object* v_inst_1532_, lean_object* v___f_1533_, lean_object* v_____r_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v_j_1529_, v___x_1535_);
v___x_1537_ = lean_array_get_size(v_cs_1530_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_nat_dec_lt(v___x_1536_, v___x_1537_);
if (v___x_1539_ == 0)
{
lean_object* v_toPure_1540_; lean_object* v___x_1541_; 
lean_dec(v___x_1536_);
lean_dec(v___f_1533_);
lean_dec_ref(v_inst_1532_);
lean_dec_ref(v_cs_1530_);
v_toPure_1540_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc(v_toPure_1540_);
lean_dec_ref(v_toApplicative_1531_);
v___x_1541_ = lean_apply_2(v_toPure_1540_, lean_box(0), v___x_1538_);
return v___x_1541_;
}
else
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_nat_dec_le(v___x_1537_, v___x_1537_);
if (v___x_1542_ == 0)
{
if (v___x_1539_ == 0)
{
lean_object* v_toPure_1543_; lean_object* v___x_1544_; 
lean_dec(v___x_1536_);
lean_dec(v___f_1533_);
lean_dec_ref(v_inst_1532_);
lean_dec_ref(v_cs_1530_);
v_toPure_1543_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc(v_toPure_1543_);
lean_dec_ref(v_toApplicative_1531_);
v___x_1544_ = lean_apply_2(v_toPure_1543_, lean_box(0), v___x_1538_);
return v___x_1544_;
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v_toApplicative_1531_);
v___x_1545_ = lean_usize_of_nat(v___x_1536_);
lean_dec(v___x_1536_);
v___x_1546_ = lean_usize_of_nat(v___x_1537_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1532_, v___f_1533_, v_cs_1530_, v___x_1545_, v___x_1546_, v___x_1538_);
return v___x_1547_;
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
lean_dec_ref(v_toApplicative_1531_);
v___x_1548_ = lean_usize_of_nat(v___x_1536_);
lean_dec(v___x_1536_);
v___x_1549_ = lean_usize_of_nat(v___x_1537_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1532_, v___f_1533_, v_cs_1530_, v___x_1548_, v___x_1549_, v___x_1538_);
return v___x_1550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_j_1551_, lean_object* v_cs_1552_, lean_object* v_toApplicative_1553_, lean_object* v_inst_1554_, lean_object* v___f_1555_, lean_object* v_____r_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_j_1551_, v_cs_1552_, v_toApplicative_1553_, v_inst_1554_, v___f_1555_, v_____r_1556_);
lean_dec(v_j_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1558_, lean_object* v_f_1559_, lean_object* v_x_1560_, size_t v_x_1561_, size_t v_x_1562_){
_start:
{
if (lean_obj_tag(v_x_1560_) == 0)
{
lean_object* v_toApplicative_1563_; lean_object* v_toBind_1564_; lean_object* v_cs_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; size_t v___x_1568_; lean_object* v_j_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_toApplicative_1563_ = lean_ctor_get(v_inst_1558_, 0);
v_toBind_1564_ = lean_ctor_get(v_inst_1558_, 1);
lean_inc(v_toBind_1564_);
v_cs_1565_ = lean_ctor_get(v_x_1560_, 0);
lean_inc_ref_n(v_cs_1565_, 2);
lean_dec_ref(v_x_1560_);
lean_inc(v_f_1559_);
lean_inc_ref_n(v_inst_1558_, 2);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1566_, 0, v_inst_1558_);
lean_closure_set(v___f_1566_, 1, v_f_1559_);
v___x_1567_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1568_ = lean_usize_shift_right(v_x_1561_, v_x_1562_);
v_j_1569_ = lean_usize_to_nat(v___x_1568_);
lean_inc_ref(v_toApplicative_1563_);
lean_inc(v_j_1569_);
v___f_1570_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1570_, 0, v_j_1569_);
lean_closure_set(v___f_1570_, 1, v_cs_1565_);
lean_closure_set(v___f_1570_, 2, v_toApplicative_1563_);
lean_closure_set(v___f_1570_, 3, v_inst_1558_);
lean_closure_set(v___f_1570_, 4, v___f_1566_);
v___x_1571_ = lean_array_get(v___x_1567_, v_cs_1565_, v_j_1569_);
lean_dec(v_j_1569_);
lean_dec_ref(v_cs_1565_);
v___x_1572_ = ((size_t)1ULL);
v___x_1573_ = lean_usize_shift_left(v___x_1572_, v_x_1562_);
v___x_1574_ = lean_usize_sub(v___x_1573_, v___x_1572_);
v___x_1575_ = lean_usize_land(v_x_1561_, v___x_1574_);
v___x_1576_ = ((size_t)5ULL);
v___x_1577_ = lean_usize_sub(v_x_1562_, v___x_1576_);
v___x_1578_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1558_, v_f_1559_, v___x_1571_, v___x_1575_, v___x_1577_);
v___x_1579_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1578_, v___f_1570_);
return v___x_1579_;
}
else
{
lean_object* v_toApplicative_1580_; lean_object* v_vs_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_toApplicative_1580_ = lean_ctor_get(v_inst_1558_, 0);
v_vs_1581_ = lean_ctor_get(v_x_1560_, 0);
lean_inc_ref(v_vs_1581_);
lean_dec_ref(v_x_1560_);
v___x_1582_ = lean_usize_to_nat(v_x_1561_);
v___x_1583_ = lean_array_get_size(v_vs_1581_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_nat_dec_lt(v___x_1582_, v___x_1583_);
if (v___x_1585_ == 0)
{
lean_object* v_toPure_1586_; lean_object* v___x_1587_; 
lean_inc_ref(v_toApplicative_1580_);
lean_dec(v___x_1582_);
lean_dec_ref(v_vs_1581_);
lean_dec(v_f_1559_);
lean_dec_ref(v_inst_1558_);
v_toPure_1586_ = lean_ctor_get(v_toApplicative_1580_, 1);
lean_inc(v_toPure_1586_);
lean_dec_ref(v_toApplicative_1580_);
v___x_1587_ = lean_apply_2(v_toPure_1586_, lean_box(0), v___x_1584_);
return v___x_1587_;
}
else
{
lean_object* v___f_1588_; uint8_t v___x_1589_; 
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1588_, 0, v_f_1559_);
v___x_1589_ = lean_nat_dec_le(v___x_1583_, v___x_1583_);
if (v___x_1589_ == 0)
{
if (v___x_1585_ == 0)
{
lean_object* v_toPure_1590_; lean_object* v___x_1591_; 
lean_inc_ref(v_toApplicative_1580_);
lean_dec_ref(v___f_1588_);
lean_dec(v___x_1582_);
lean_dec_ref(v_vs_1581_);
lean_dec_ref(v_inst_1558_);
v_toPure_1590_ = lean_ctor_get(v_toApplicative_1580_, 1);
lean_inc(v_toPure_1590_);
lean_dec_ref(v_toApplicative_1580_);
v___x_1591_ = lean_apply_2(v_toPure_1590_, lean_box(0), v___x_1584_);
return v___x_1591_;
}
else
{
size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_usize_of_nat(v___x_1582_);
lean_dec(v___x_1582_);
v___x_1593_ = lean_usize_of_nat(v___x_1583_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1558_, v___f_1588_, v_vs_1581_, v___x_1592_, v___x_1593_, v___x_1584_);
return v___x_1594_;
}
}
else
{
size_t v___x_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_usize_of_nat(v___x_1582_);
lean_dec(v___x_1582_);
v___x_1596_ = lean_usize_of_nat(v___x_1583_);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1558_, v___f_1588_, v_vs_1581_, v___x_1595_, v___x_1596_, v___x_1584_);
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1598_, lean_object* v_f_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
size_t v_x_290__boxed_1603_; size_t v_x_291__boxed_1604_; lean_object* v_res_1605_; 
v_x_290__boxed_1603_ = lean_unbox_usize(v_x_1601_);
lean_dec(v_x_1601_);
v_x_291__boxed_1604_ = lean_unbox_usize(v_x_1602_);
lean_dec(v_x_1602_);
v_res_1605_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1598_, v_f_1599_, v_x_1600_, v_x_290__boxed_1603_, v_x_291__boxed_1604_);
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
size_t v_x_360__boxed_1621_; size_t v_x_361__boxed_1622_; lean_object* v_res_1623_; 
v_x_360__boxed_1621_ = lean_unbox_usize(v_x_1619_);
lean_dec(v_x_1619_);
v_x_361__boxed_1622_ = lean_unbox_usize(v_x_1620_);
lean_dec(v_x_1620_);
v_res_1623_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1614_, v_m_1615_, v_inst_1616_, v_f_1617_, v_x_1618_, v_x_360__boxed_1621_, v_x_361__boxed_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_tail_1624_, lean_object* v___x_1625_, lean_object* v_toApplicative_1626_, lean_object* v_inst_1627_, lean_object* v___f_1628_, lean_object* v_____r_1629_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1630_ = lean_array_get_size(v_tail_1624_);
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_nat_dec_lt(v___x_1625_, v___x_1630_);
if (v___x_1632_ == 0)
{
lean_object* v_toPure_1633_; lean_object* v___x_1634_; 
lean_dec(v___f_1628_);
lean_dec_ref(v_inst_1627_);
lean_dec_ref(v_tail_1624_);
v_toPure_1633_ = lean_ctor_get(v_toApplicative_1626_, 1);
lean_inc(v_toPure_1633_);
lean_dec_ref(v_toApplicative_1626_);
v___x_1634_ = lean_apply_2(v_toPure_1633_, lean_box(0), v___x_1631_);
return v___x_1634_;
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_nat_dec_le(v___x_1630_, v___x_1630_);
if (v___x_1635_ == 0)
{
if (v___x_1632_ == 0)
{
lean_object* v_toPure_1636_; lean_object* v___x_1637_; 
lean_dec(v___f_1628_);
lean_dec_ref(v_inst_1627_);
lean_dec_ref(v_tail_1624_);
v_toPure_1636_ = lean_ctor_get(v_toApplicative_1626_, 1);
lean_inc(v_toPure_1636_);
lean_dec_ref(v_toApplicative_1626_);
v___x_1637_ = lean_apply_2(v_toPure_1636_, lean_box(0), v___x_1631_);
return v___x_1637_;
}
else
{
size_t v___x_1638_; size_t v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_toApplicative_1626_);
v___x_1638_ = ((size_t)0ULL);
v___x_1639_ = lean_usize_of_nat(v___x_1630_);
v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1627_, v___f_1628_, v_tail_1624_, v___x_1638_, v___x_1639_, v___x_1631_);
return v___x_1640_;
}
}
else
{
size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v_toApplicative_1626_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = lean_usize_of_nat(v___x_1630_);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1627_, v___f_1628_, v_tail_1624_, v___x_1641_, v___x_1642_, v___x_1631_);
return v___x_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_tail_1644_, lean_object* v___x_1645_, lean_object* v_toApplicative_1646_, lean_object* v_inst_1647_, lean_object* v___f_1648_, lean_object* v_____r_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_tail_1644_, v___x_1645_, v_toApplicative_1646_, v_inst_1647_, v___f_1648_, v_____r_1649_);
lean_dec(v___x_1645_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1651_, lean_object* v_t_1652_, lean_object* v_f_1653_, lean_object* v_start_1654_){
_start:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = lean_nat_dec_eq(v_start_1654_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v_root_1657_; lean_object* v_tail_1658_; size_t v_shift_1659_; lean_object* v_tailOff_1660_; uint8_t v___x_1661_; 
v_root_1657_ = lean_ctor_get(v_t_1652_, 0);
lean_inc_ref(v_root_1657_);
v_tail_1658_ = lean_ctor_get(v_t_1652_, 1);
lean_inc_ref(v_tail_1658_);
v_shift_1659_ = lean_ctor_get_usize(v_t_1652_, 4);
v_tailOff_1660_ = lean_ctor_get(v_t_1652_, 3);
lean_inc(v_tailOff_1660_);
lean_dec_ref(v_t_1652_);
v___x_1661_ = lean_nat_dec_le(v_tailOff_1660_, v_start_1654_);
if (v___x_1661_ == 0)
{
lean_object* v_toApplicative_1662_; lean_object* v_toBind_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; size_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v_tailOff_1660_);
v_toApplicative_1662_ = lean_ctor_get(v_inst_1651_, 0);
v_toBind_1663_ = lean_ctor_get(v_inst_1651_, 1);
lean_inc(v_toBind_1663_);
lean_inc(v_f_1653_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1664_, 0, v_f_1653_);
lean_inc_ref(v_inst_1651_);
lean_inc_ref(v_toApplicative_1662_);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1665_, 0, v_tail_1658_);
lean_closure_set(v___f_1665_, 1, v___x_1655_);
lean_closure_set(v___f_1665_, 2, v_toApplicative_1662_);
lean_closure_set(v___f_1665_, 3, v_inst_1651_);
lean_closure_set(v___f_1665_, 4, v___f_1664_);
v___x_1666_ = lean_usize_of_nat(v_start_1654_);
v___x_1667_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1651_, v_f_1653_, v_root_1657_, v___x_1666_, v_shift_1659_);
v___x_1668_ = lean_apply_4(v_toBind_1663_, lean_box(0), lean_box(0), v___x_1667_, v___f_1665_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
lean_dec_ref(v_root_1657_);
v___x_1669_ = lean_nat_sub(v_start_1654_, v_tailOff_1660_);
lean_dec(v_tailOff_1660_);
v___x_1670_ = lean_array_get_size(v_tail_1658_);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_nat_dec_lt(v___x_1669_, v___x_1670_);
if (v___x_1672_ == 0)
{
lean_object* v_toApplicative_1673_; lean_object* v_toPure_1674_; lean_object* v___x_1675_; 
lean_dec(v___x_1669_);
lean_dec_ref(v_tail_1658_);
lean_dec(v_f_1653_);
v_toApplicative_1673_ = lean_ctor_get(v_inst_1651_, 0);
lean_inc_ref(v_toApplicative_1673_);
lean_dec_ref(v_inst_1651_);
v_toPure_1674_ = lean_ctor_get(v_toApplicative_1673_, 1);
lean_inc(v_toPure_1674_);
lean_dec_ref(v_toApplicative_1673_);
v___x_1675_ = lean_apply_2(v_toPure_1674_, lean_box(0), v___x_1671_);
return v___x_1675_;
}
else
{
lean_object* v___f_1676_; uint8_t v___x_1677_; 
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1676_, 0, v_f_1653_);
v___x_1677_ = lean_nat_dec_le(v___x_1670_, v___x_1670_);
if (v___x_1677_ == 0)
{
if (v___x_1672_ == 0)
{
lean_object* v_toApplicative_1678_; lean_object* v_toPure_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v___f_1676_);
lean_dec(v___x_1669_);
lean_dec_ref(v_tail_1658_);
v_toApplicative_1678_ = lean_ctor_get(v_inst_1651_, 0);
lean_inc_ref(v_toApplicative_1678_);
lean_dec_ref(v_inst_1651_);
v_toPure_1679_ = lean_ctor_get(v_toApplicative_1678_, 1);
lean_inc(v_toPure_1679_);
lean_dec_ref(v_toApplicative_1678_);
v___x_1680_ = lean_apply_2(v_toPure_1679_, lean_box(0), v___x_1671_);
return v___x_1680_;
}
else
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_usize_of_nat(v___x_1669_);
lean_dec(v___x_1669_);
v___x_1682_ = lean_usize_of_nat(v___x_1670_);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1651_, v___f_1676_, v_tail_1658_, v___x_1681_, v___x_1682_, v___x_1671_);
return v___x_1683_;
}
}
else
{
size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_usize_of_nat(v___x_1669_);
lean_dec(v___x_1669_);
v___x_1685_ = lean_usize_of_nat(v___x_1670_);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1651_, v___f_1676_, v_tail_1658_, v___x_1684_, v___x_1685_, v___x_1671_);
return v___x_1686_;
}
}
}
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1651_, v_t_1652_, v_f_1653_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1688_, lean_object* v_t_1689_, lean_object* v_f_1690_, lean_object* v_start_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_PersistentArray_forM___redArg(v_inst_1688_, v_t_1689_, v_f_1690_, v_start_1691_);
lean_dec(v_start_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1693_, lean_object* v_m_1694_, lean_object* v_inst_1695_, lean_object* v_t_1696_, lean_object* v_f_1697_, lean_object* v_start_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_PersistentArray_forM___redArg(v_inst_1695_, v_t_1696_, v_f_1697_, v_start_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_m_1701_, lean_object* v_inst_1702_, lean_object* v_t_1703_, lean_object* v_f_1704_, lean_object* v_start_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_PersistentArray_forM(v_00_u03b1_1700_, v_m_1701_, v_inst_1702_, v_t_1703_, v_f_1704_, v_start_1705_);
lean_dec(v_start_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1707_, lean_object* v_x1_1708_, lean_object* v_x2_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_apply_2(v_f_1707_, v_x1_1708_, v_x2_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1730_, lean_object* v_f_1731_, lean_object* v_init_1732_, lean_object* v_start_1733_){
_start:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1734_, 0, v_f_1731_);
v___x_1735_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1736_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1735_, v_t_1730_, v___f_1734_, v_init_1732_, v_start_1733_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1737_, lean_object* v_f_1738_, lean_object* v_init_1739_, lean_object* v_start_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_PersistentArray_foldl___redArg(v_t_1737_, v_f_1738_, v_init_1739_, v_start_1740_);
lean_dec(v_start_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_t_1744_, lean_object* v_f_1745_, lean_object* v_init_1746_, lean_object* v_start_1747_){
_start:
{
lean_object* v___f_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___f_1748_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1748_, 0, v_f_1745_);
v___x_1749_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1750_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1749_, v_t_1744_, v___f_1748_, v_init_1746_, v_start_1747_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_t_1753_, lean_object* v_f_1754_, lean_object* v_init_1755_, lean_object* v_start_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1751_, v_00_u03b2_1752_, v_t_1753_, v_f_1754_, v_init_1755_, v_start_1756_);
lean_dec(v_start_1756_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1758_, lean_object* v_f_1759_, lean_object* v_init_1760_){
_start:
{
lean_object* v___f_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1761_, 0, v_f_1759_);
v___x_1762_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1763_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1762_, v_t_1758_, v___f_1761_, v_init_1760_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_t_1766_, lean_object* v_f_1767_, lean_object* v_init_1768_){
_start:
{
lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1769_, 0, v_f_1767_);
v___x_1770_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1771_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1770_, v_t_1766_, v___f_1769_, v_init_1768_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1772_, lean_object* v_x1_1773_, lean_object* v_x2_1774_){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
lean_inc(v_x2_1774_);
v___x_1775_ = lean_apply_1(v_p_1772_, v_x2_1774_);
v___x_1776_ = lean_unbox(v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec(v_x2_1774_);
return v_x1_1773_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_PersistentArray_push___redArg(v_x1_1773_, v_x2_1774_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1778_, lean_object* v_p_1779_){
_start:
{
lean_object* v___f_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1780_, 0, v_p_1779_);
v___x_1781_ = lean_unsigned_to_nat(32u);
v___x_1782_ = lean_mk_empty_array_with_capacity(v___x_1781_);
lean_dec_ref(v___x_1782_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__1, &l_Lean_PersistentArray_empty___closed__1_once, _init_l_Lean_PersistentArray_empty___closed__1);
v___x_1785_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1786_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1785_, v_as_1778_, v___f_1780_, v___x_1784_, v___x_1783_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1787_, lean_object* v_as_1788_, lean_object* v_p_1789_){
_start:
{
lean_object* v___f_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___f_1790_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1790_, 0, v_p_1789_);
v___x_1791_ = lean_unsigned_to_nat(32u);
v___x_1792_ = lean_mk_empty_array_with_capacity(v___x_1791_);
lean_dec_ref(v___x_1792_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__1, &l_Lean_PersistentArray_empty___closed__1_once, _init_l_Lean_PersistentArray_empty___closed__1);
v___x_1795_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1796_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1795_, v_as_1788_, v___f_1790_, v___x_1794_, v___x_1793_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1797_, size_t v_i_1798_, size_t v_stop_1799_, lean_object* v_b_1800_){
_start:
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_usize_dec_eq(v_i_1798_, v_stop_1799_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; 
v___x_1802_ = lean_array_uget_borrowed(v_as_1797_, v_i_1798_);
lean_inc(v___x_1802_);
v___x_1803_ = lean_array_push(v_b_1800_, v___x_1802_);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1798_, v___x_1804_);
v_i_1798_ = v___x_1805_;
v_b_1800_ = v___x_1803_;
goto _start;
}
else
{
return v_b_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1807_, lean_object* v_i_1808_, lean_object* v_stop_1809_, lean_object* v_b_1810_){
_start:
{
size_t v_i_boxed_1811_; size_t v_stop_boxed_1812_; lean_object* v_res_1813_; 
v_i_boxed_1811_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_stop_boxed_1812_ = lean_unbox_usize(v_stop_1809_);
lean_dec(v_stop_1809_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1807_, v_i_boxed_1811_, v_stop_boxed_1812_, v_b_1810_);
lean_dec_ref(v_as_1807_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 0)
{
lean_object* v_cs_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_cs_1816_ = lean_ctor_get(v_x_1814_, 0);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_array_get_size(v_cs_1816_);
v___x_1819_ = lean_nat_dec_lt(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
return v_x_1815_;
}
else
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_nat_dec_le(v___x_1818_, v___x_1818_);
if (v___x_1820_ == 0)
{
if (v___x_1819_ == 0)
{
return v_x_1815_;
}
else
{
size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = lean_usize_of_nat(v___x_1818_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1816_, v___x_1821_, v___x_1822_, v_x_1815_);
return v___x_1823_;
}
}
else
{
size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = lean_usize_of_nat(v___x_1818_);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1816_, v___x_1824_, v___x_1825_, v_x_1815_);
return v___x_1826_;
}
}
}
else
{
lean_object* v_vs_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_vs_1827_ = lean_ctor_get(v_x_1814_, 0);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_array_get_size(v_vs_1827_);
v___x_1830_ = lean_nat_dec_lt(v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
return v_x_1815_;
}
else
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_le(v___x_1829_, v___x_1829_);
if (v___x_1831_ == 0)
{
if (v___x_1830_ == 0)
{
return v_x_1815_;
}
else
{
size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((size_t)0ULL);
v___x_1833_ = lean_usize_of_nat(v___x_1829_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1827_, v___x_1832_, v___x_1833_, v_x_1815_);
return v___x_1834_;
}
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1829_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1827_, v___x_1835_, v___x_1836_, v_x_1815_);
return v___x_1837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1838_, size_t v_i_1839_, size_t v_stop_1840_, lean_object* v_b_1841_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_eq(v_i_1839_, v_stop_1840_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; size_t v___x_1845_; size_t v___x_1846_; 
v___x_1843_ = lean_array_uget_borrowed(v_as_1838_, v_i_1839_);
v___x_1844_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1843_, v_b_1841_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1839_, v___x_1845_);
v_i_1839_ = v___x_1846_;
v_b_1841_ = v___x_1844_;
goto _start;
}
else
{
return v_b_1841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1848_, lean_object* v_i_1849_, lean_object* v_stop_1850_, lean_object* v_b_1851_){
_start:
{
size_t v_i_boxed_1852_; size_t v_stop_boxed_1853_; lean_object* v_res_1854_; 
v_i_boxed_1852_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_stop_boxed_1853_ = lean_unbox_usize(v_stop_1850_);
lean_dec(v_stop_1850_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1848_, v_i_boxed_1852_, v_stop_boxed_1853_, v_b_1851_);
lean_dec_ref(v_as_1848_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1855_, v_x_1856_);
lean_dec_ref(v_x_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1858_, size_t v_x_1859_, size_t v_x_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
lean_object* v_cs_1862_; lean_object* v___x_1863_; size_t v___x_1864_; lean_object* v_j_1865_; lean_object* v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_cs_1862_ = lean_ctor_get(v_x_1858_, 0);
v___x_1863_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1864_ = lean_usize_shift_right(v_x_1859_, v_x_1860_);
v_j_1865_ = lean_usize_to_nat(v___x_1864_);
v___x_1866_ = lean_array_get_borrowed(v___x_1863_, v_cs_1862_, v_j_1865_);
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_shift_left(v___x_1867_, v_x_1860_);
v___x_1869_ = lean_usize_sub(v___x_1868_, v___x_1867_);
v___x_1870_ = lean_usize_land(v_x_1859_, v___x_1869_);
v___x_1871_ = ((size_t)5ULL);
v___x_1872_ = lean_usize_sub(v_x_1860_, v___x_1871_);
v___x_1873_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1866_, v___x_1870_, v___x_1872_, v_x_1861_);
v___x_1874_ = lean_unsigned_to_nat(1u);
v___x_1875_ = lean_nat_add(v_j_1865_, v___x_1874_);
lean_dec(v_j_1865_);
v___x_1876_ = lean_array_get_size(v_cs_1862_);
v___x_1877_ = lean_nat_dec_lt(v___x_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_dec(v___x_1875_);
return v___x_1873_;
}
else
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_nat_dec_le(v___x_1876_, v___x_1876_);
if (v___x_1878_ == 0)
{
if (v___x_1877_ == 0)
{
lean_dec(v___x_1875_);
return v___x_1873_;
}
else
{
size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_usize_of_nat(v___x_1875_);
lean_dec(v___x_1875_);
v___x_1880_ = lean_usize_of_nat(v___x_1876_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1862_, v___x_1879_, v___x_1880_, v___x_1873_);
return v___x_1881_;
}
}
else
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_usize_of_nat(v___x_1875_);
lean_dec(v___x_1875_);
v___x_1883_ = lean_usize_of_nat(v___x_1876_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1862_, v___x_1882_, v___x_1883_, v___x_1873_);
return v___x_1884_;
}
}
}
else
{
lean_object* v_vs_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v_vs_1885_ = lean_ctor_get(v_x_1858_, 0);
v___x_1886_ = lean_usize_to_nat(v_x_1859_);
v___x_1887_ = lean_array_get_size(v_vs_1885_);
v___x_1888_ = lean_nat_dec_lt(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_dec(v___x_1886_);
return v_x_1861_;
}
else
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_nat_dec_le(v___x_1887_, v___x_1887_);
if (v___x_1889_ == 0)
{
if (v___x_1888_ == 0)
{
lean_dec(v___x_1886_);
return v_x_1861_;
}
else
{
size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_usize_of_nat(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1891_ = lean_usize_of_nat(v___x_1887_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1885_, v___x_1890_, v___x_1891_, v_x_1861_);
return v___x_1892_;
}
}
else
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_usize_of_nat(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1894_ = lean_usize_of_nat(v___x_1887_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1885_, v___x_1893_, v___x_1894_, v_x_1861_);
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
size_t v_x_1497__boxed_1900_; size_t v_x_1498__boxed_1901_; lean_object* v_res_1902_; 
v_x_1497__boxed_1900_ = lean_unbox_usize(v_x_1897_);
lean_dec(v_x_1897_);
v_x_1498__boxed_1901_ = lean_unbox_usize(v_x_1898_);
lean_dec(v_x_1898_);
v_res_1902_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1896_, v_x_1497__boxed_1900_, v_x_1498__boxed_1901_, v_x_1899_);
lean_dec_ref(v_x_1896_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1903_, lean_object* v_init_1904_, lean_object* v_start_1905_){
_start:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_nat_dec_eq(v_start_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v_root_1908_; lean_object* v_tail_1909_; size_t v_shift_1910_; lean_object* v_tailOff_1911_; uint8_t v___x_1912_; 
v_root_1908_ = lean_ctor_get(v_t_1903_, 0);
v_tail_1909_ = lean_ctor_get(v_t_1903_, 1);
v_shift_1910_ = lean_ctor_get_usize(v_t_1903_, 4);
v_tailOff_1911_ = lean_ctor_get(v_t_1903_, 3);
v___x_1912_ = lean_nat_dec_le(v_tailOff_1911_, v_start_1905_);
if (v___x_1912_ == 0)
{
size_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1913_ = lean_usize_of_nat(v_start_1905_);
v___x_1914_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1908_, v___x_1913_, v_shift_1910_, v_init_1904_);
v___x_1915_ = lean_array_get_size(v_tail_1909_);
v___x_1916_ = lean_nat_dec_lt(v___x_1906_, v___x_1915_);
if (v___x_1916_ == 0)
{
return v___x_1914_;
}
else
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_nat_dec_le(v___x_1915_, v___x_1915_);
if (v___x_1917_ == 0)
{
if (v___x_1916_ == 0)
{
return v___x_1914_;
}
else
{
size_t v___x_1918_; size_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1915_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1909_, v___x_1918_, v___x_1919_, v___x_1914_);
return v___x_1920_;
}
}
else
{
size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = lean_usize_of_nat(v___x_1915_);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1909_, v___x_1921_, v___x_1922_, v___x_1914_);
return v___x_1923_;
}
}
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = lean_nat_sub(v_start_1905_, v_tailOff_1911_);
v___x_1925_ = lean_array_get_size(v_tail_1909_);
v___x_1926_ = lean_nat_dec_lt(v___x_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_dec(v___x_1924_);
return v_init_1904_;
}
else
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_nat_dec_le(v___x_1925_, v___x_1925_);
if (v___x_1927_ == 0)
{
if (v___x_1926_ == 0)
{
lean_dec(v___x_1924_);
return v_init_1904_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_usize_of_nat(v___x_1924_);
lean_dec(v___x_1924_);
v___x_1929_ = lean_usize_of_nat(v___x_1925_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1909_, v___x_1928_, v___x_1929_, v_init_1904_);
return v___x_1930_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_usize_of_nat(v___x_1924_);
lean_dec(v___x_1924_);
v___x_1932_ = lean_usize_of_nat(v___x_1925_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1909_, v___x_1931_, v___x_1932_, v_init_1904_);
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_root_1934_; lean_object* v_tail_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_root_1934_ = lean_ctor_get(v_t_1903_, 0);
v_tail_1935_ = lean_ctor_get(v_t_1903_, 1);
v___x_1936_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1934_, v_init_1904_);
v___x_1937_ = lean_array_get_size(v_tail_1935_);
v___x_1938_ = lean_nat_dec_lt(v___x_1906_, v___x_1937_);
if (v___x_1938_ == 0)
{
return v___x_1936_;
}
else
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_nat_dec_le(v___x_1937_, v___x_1937_);
if (v___x_1939_ == 0)
{
if (v___x_1938_ == 0)
{
return v___x_1936_;
}
else
{
size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = lean_usize_of_nat(v___x_1937_);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1935_, v___x_1940_, v___x_1941_, v___x_1936_);
return v___x_1942_;
}
}
else
{
size_t v___x_1943_; size_t v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = lean_usize_of_nat(v___x_1937_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1935_, v___x_1943_, v___x_1944_, v___x_1936_);
return v___x_1945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1946_, lean_object* v_init_1947_, lean_object* v_start_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1946_, v_init_1947_, v_start_1948_);
lean_dec(v_start_1948_);
lean_dec_ref(v_t_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1953_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1950_, v___x_1952_, v___x_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_PersistentArray_toArray___redArg(v_t_1954_);
lean_dec_ref(v_t_1954_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1956_, lean_object* v_t_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentArray_toArray___redArg(v_t_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_t_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1959_, v_t_1960_);
lean_dec_ref(v_t_1960_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1962_, lean_object* v_t_1963_, lean_object* v_init_1964_, lean_object* v_start_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1963_, v_init_1964_, v_start_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1967_, lean_object* v_t_1968_, lean_object* v_init_1969_, lean_object* v_start_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1967_, v_t_1968_, v_init_1969_, v_start_1970_);
lean_dec(v_start_1970_);
lean_dec_ref(v_t_1968_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1972_, lean_object* v_x_1973_, size_t v_x_1974_, size_t v_x_1975_, lean_object* v_x_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1973_, v_x_1974_, v_x_1975_, v_x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
size_t v_x_1655__boxed_1983_; size_t v_x_1656__boxed_1984_; lean_object* v_res_1985_; 
v_x_1655__boxed_1983_ = lean_unbox_usize(v_x_1980_);
lean_dec(v_x_1980_);
v_x_1656__boxed_1984_ = lean_unbox_usize(v_x_1981_);
lean_dec(v_x_1981_);
v_res_1985_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1978_, v_x_1979_, v_x_1655__boxed_1983_, v_x_1656__boxed_1984_, v_x_1982_);
lean_dec_ref(v_x_1979_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1986_, lean_object* v_as_1987_, size_t v_i_1988_, size_t v_stop_1989_, lean_object* v_b_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1987_, v_i_1988_, v_stop_1989_, v_b_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1992_, lean_object* v_as_1993_, lean_object* v_i_1994_, lean_object* v_stop_1995_, lean_object* v_b_1996_){
_start:
{
size_t v_i_boxed_1997_; size_t v_stop_boxed_1998_; lean_object* v_res_1999_; 
v_i_boxed_1997_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_stop_boxed_1998_ = lean_unbox_usize(v_stop_1995_);
lean_dec(v_stop_1995_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1992_, v_as_1993_, v_i_boxed_1997_, v_stop_boxed_1998_, v_b_1996_);
lean_dec_ref(v_as_1993_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_2001_, v_x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_2004_, v_x_2005_, v_x_2006_);
lean_dec_ref(v_x_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2008_, lean_object* v_as_2009_, size_t v_i_2010_, size_t v_stop_2011_, lean_object* v_b_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_2009_, v_i_2010_, v_stop_2011_, v_b_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2014_, lean_object* v_as_2015_, lean_object* v_i_2016_, lean_object* v_stop_2017_, lean_object* v_b_2018_){
_start:
{
size_t v_i_boxed_2019_; size_t v_stop_boxed_2020_; lean_object* v_res_2021_; 
v_i_boxed_2019_ = lean_unbox_usize(v_i_2016_);
lean_dec(v_i_2016_);
v_stop_boxed_2020_ = lean_unbox_usize(v_stop_2017_);
lean_dec(v_stop_2017_);
v_res_2021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_2014_, v_as_2015_, v_i_boxed_2019_, v_stop_boxed_2020_, v_b_2018_);
lean_dec_ref(v_as_2015_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_2022_, size_t v_i_2023_, size_t v_stop_2024_, lean_object* v_b_2025_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_eq(v_i_2023_, v_stop_2024_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; 
v___x_2027_ = lean_array_uget_borrowed(v_as_2022_, v_i_2023_);
lean_inc(v___x_2027_);
v___x_2028_ = l_Lean_PersistentArray_push___redArg(v_b_2025_, v___x_2027_);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_2023_, v___x_2029_);
v_i_2023_ = v___x_2030_;
v_b_2025_ = v___x_2028_;
goto _start;
}
else
{
return v_b_2025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2032_, lean_object* v_i_2033_, lean_object* v_stop_2034_, lean_object* v_b_2035_){
_start:
{
size_t v_i_boxed_2036_; size_t v_stop_boxed_2037_; lean_object* v_res_2038_; 
v_i_boxed_2036_ = lean_unbox_usize(v_i_2033_);
lean_dec(v_i_2033_);
v_stop_boxed_2037_ = lean_unbox_usize(v_stop_2034_);
lean_dec(v_stop_2034_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2032_, v_i_boxed_2036_, v_stop_boxed_2037_, v_b_2035_);
lean_dec_ref(v_as_2032_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
lean_object* v_cs_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_cs_2041_ = lean_ctor_get(v_x_2039_, 0);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_array_get_size(v_cs_2041_);
v___x_2044_ = lean_nat_dec_lt(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
return v_x_2040_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_nat_dec_le(v___x_2043_, v___x_2043_);
if (v___x_2045_ == 0)
{
if (v___x_2044_ == 0)
{
return v_x_2040_;
}
else
{
size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = ((size_t)0ULL);
v___x_2047_ = lean_usize_of_nat(v___x_2043_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2041_, v___x_2046_, v___x_2047_, v_x_2040_);
return v___x_2048_;
}
}
else
{
size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = ((size_t)0ULL);
v___x_2050_ = lean_usize_of_nat(v___x_2043_);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2041_, v___x_2049_, v___x_2050_, v_x_2040_);
return v___x_2051_;
}
}
}
else
{
lean_object* v_vs_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_vs_2052_ = lean_ctor_get(v_x_2039_, 0);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_array_get_size(v_vs_2052_);
v___x_2055_ = lean_nat_dec_lt(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
return v_x_2040_;
}
else
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_nat_dec_le(v___x_2054_, v___x_2054_);
if (v___x_2056_ == 0)
{
if (v___x_2055_ == 0)
{
return v_x_2040_;
}
else
{
size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = lean_usize_of_nat(v___x_2054_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2052_, v___x_2057_, v___x_2058_, v_x_2040_);
return v___x_2059_;
}
}
else
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = ((size_t)0ULL);
v___x_2061_ = lean_usize_of_nat(v___x_2054_);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2052_, v___x_2060_, v___x_2061_, v_x_2040_);
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2063_, size_t v_i_2064_, size_t v_stop_2065_, lean_object* v_b_2066_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_eq(v_i_2064_, v_stop_2065_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; 
v___x_2068_ = lean_array_uget_borrowed(v_as_2063_, v_i_2064_);
v___x_2069_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2068_, v_b_2066_);
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2064_, v___x_2070_);
v_i_2064_ = v___x_2071_;
v_b_2066_ = v___x_2069_;
goto _start;
}
else
{
return v_b_2066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2073_, lean_object* v_i_2074_, lean_object* v_stop_2075_, lean_object* v_b_2076_){
_start:
{
size_t v_i_boxed_2077_; size_t v_stop_boxed_2078_; lean_object* v_res_2079_; 
v_i_boxed_2077_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_stop_boxed_2078_ = lean_unbox_usize(v_stop_2075_);
lean_dec(v_stop_2075_);
v_res_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2073_, v_i_boxed_2077_, v_stop_boxed_2078_, v_b_2076_);
lean_dec_ref(v_as_2073_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2080_, v_x_2081_);
lean_dec_ref(v_x_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2083_, size_t v_x_2084_, size_t v_x_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
lean_object* v_cs_2087_; lean_object* v___x_2088_; size_t v___x_2089_; lean_object* v_j_2090_; lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_cs_2087_ = lean_ctor_get(v_x_2083_, 0);
v___x_2088_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2089_ = lean_usize_shift_right(v_x_2084_, v_x_2085_);
v_j_2090_ = lean_usize_to_nat(v___x_2089_);
v___x_2091_ = lean_array_get_borrowed(v___x_2088_, v_cs_2087_, v_j_2090_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_shift_left(v___x_2092_, v_x_2085_);
v___x_2094_ = lean_usize_sub(v___x_2093_, v___x_2092_);
v___x_2095_ = lean_usize_land(v_x_2084_, v___x_2094_);
v___x_2096_ = ((size_t)5ULL);
v___x_2097_ = lean_usize_sub(v_x_2085_, v___x_2096_);
v___x_2098_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2091_, v___x_2095_, v___x_2097_, v_x_2086_);
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_j_2090_, v___x_2099_);
lean_dec(v_j_2090_);
v___x_2101_ = lean_array_get_size(v_cs_2087_);
v___x_2102_ = lean_nat_dec_lt(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_dec(v___x_2100_);
return v___x_2098_;
}
else
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_nat_dec_le(v___x_2101_, v___x_2101_);
if (v___x_2103_ == 0)
{
if (v___x_2102_ == 0)
{
lean_dec(v___x_2100_);
return v___x_2098_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = lean_usize_of_nat(v___x_2100_);
lean_dec(v___x_2100_);
v___x_2105_ = lean_usize_of_nat(v___x_2101_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2087_, v___x_2104_, v___x_2105_, v___x_2098_);
return v___x_2106_;
}
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_usize_of_nat(v___x_2100_);
lean_dec(v___x_2100_);
v___x_2108_ = lean_usize_of_nat(v___x_2101_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2087_, v___x_2107_, v___x_2108_, v___x_2098_);
return v___x_2109_;
}
}
}
else
{
lean_object* v_vs_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_vs_2110_ = lean_ctor_get(v_x_2083_, 0);
v___x_2111_ = lean_usize_to_nat(v_x_2084_);
v___x_2112_ = lean_array_get_size(v_vs_2110_);
v___x_2113_ = lean_nat_dec_lt(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec(v___x_2111_);
return v_x_2086_;
}
else
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_nat_dec_le(v___x_2112_, v___x_2112_);
if (v___x_2114_ == 0)
{
if (v___x_2113_ == 0)
{
lean_dec(v___x_2111_);
return v_x_2086_;
}
else
{
size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_usize_of_nat(v___x_2111_);
lean_dec(v___x_2111_);
v___x_2116_ = lean_usize_of_nat(v___x_2112_);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2110_, v___x_2115_, v___x_2116_, v_x_2086_);
return v___x_2117_;
}
}
else
{
size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_usize_of_nat(v___x_2111_);
lean_dec(v___x_2111_);
v___x_2119_ = lean_usize_of_nat(v___x_2112_);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2110_, v___x_2118_, v___x_2119_, v_x_2086_);
return v___x_2120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
size_t v_x_1523__boxed_2125_; size_t v_x_1524__boxed_2126_; lean_object* v_res_2127_; 
v_x_1523__boxed_2125_ = lean_unbox_usize(v_x_2122_);
lean_dec(v_x_2122_);
v_x_1524__boxed_2126_ = lean_unbox_usize(v_x_2123_);
lean_dec(v_x_2123_);
v_res_2127_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2121_, v_x_1523__boxed_2125_, v_x_1524__boxed_2126_, v_x_2124_);
lean_dec_ref(v_x_2121_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2128_, lean_object* v_init_2129_, lean_object* v_start_2130_){
_start:
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_nat_dec_eq(v_start_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v_root_2133_; lean_object* v_tail_2134_; size_t v_shift_2135_; lean_object* v_tailOff_2136_; uint8_t v___x_2137_; 
v_root_2133_ = lean_ctor_get(v_t_2128_, 0);
v_tail_2134_ = lean_ctor_get(v_t_2128_, 1);
v_shift_2135_ = lean_ctor_get_usize(v_t_2128_, 4);
v_tailOff_2136_ = lean_ctor_get(v_t_2128_, 3);
v___x_2137_ = lean_nat_dec_le(v_tailOff_2136_, v_start_2130_);
if (v___x_2137_ == 0)
{
size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2138_ = lean_usize_of_nat(v_start_2130_);
v___x_2139_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2133_, v___x_2138_, v_shift_2135_, v_init_2129_);
v___x_2140_ = lean_array_get_size(v_tail_2134_);
v___x_2141_ = lean_nat_dec_lt(v___x_2131_, v___x_2140_);
if (v___x_2141_ == 0)
{
return v___x_2139_;
}
else
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_nat_dec_le(v___x_2140_, v___x_2140_);
if (v___x_2142_ == 0)
{
if (v___x_2141_ == 0)
{
return v___x_2139_;
}
else
{
size_t v___x_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = lean_usize_of_nat(v___x_2140_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2134_, v___x_2143_, v___x_2144_, v___x_2139_);
return v___x_2145_;
}
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2140_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2134_, v___x_2146_, v___x_2147_, v___x_2139_);
return v___x_2148_;
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = lean_nat_sub(v_start_2130_, v_tailOff_2136_);
v___x_2150_ = lean_array_get_size(v_tail_2134_);
v___x_2151_ = lean_nat_dec_lt(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec(v___x_2149_);
return v_init_2129_;
}
else
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_nat_dec_le(v___x_2150_, v___x_2150_);
if (v___x_2152_ == 0)
{
if (v___x_2151_ == 0)
{
lean_dec(v___x_2149_);
return v_init_2129_;
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_usize_of_nat(v___x_2149_);
lean_dec(v___x_2149_);
v___x_2154_ = lean_usize_of_nat(v___x_2150_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2134_, v___x_2153_, v___x_2154_, v_init_2129_);
return v___x_2155_;
}
}
else
{
size_t v___x_2156_; size_t v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_usize_of_nat(v___x_2149_);
lean_dec(v___x_2149_);
v___x_2157_ = lean_usize_of_nat(v___x_2150_);
v___x_2158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2134_, v___x_2156_, v___x_2157_, v_init_2129_);
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_root_2159_; lean_object* v_tail_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v_root_2159_ = lean_ctor_get(v_t_2128_, 0);
v_tail_2160_ = lean_ctor_get(v_t_2128_, 1);
v___x_2161_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2159_, v_init_2129_);
v___x_2162_ = lean_array_get_size(v_tail_2160_);
v___x_2163_ = lean_nat_dec_lt(v___x_2131_, v___x_2162_);
if (v___x_2163_ == 0)
{
return v___x_2161_;
}
else
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_nat_dec_le(v___x_2162_, v___x_2162_);
if (v___x_2164_ == 0)
{
if (v___x_2163_ == 0)
{
return v___x_2161_;
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = lean_usize_of_nat(v___x_2162_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2160_, v___x_2165_, v___x_2166_, v___x_2161_);
return v___x_2167_;
}
}
else
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = lean_usize_of_nat(v___x_2162_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2160_, v___x_2168_, v___x_2169_, v___x_2161_);
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2171_, lean_object* v_init_2172_, lean_object* v_start_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2171_, v_init_2172_, v_start_2173_);
lean_dec(v_start_2173_);
lean_dec_ref(v_t_2171_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2175_, lean_object* v_t_u2082_2176_){
_start:
{
uint8_t v___x_2177_; 
v___x_2177_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2175_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2176_, v_t_u2081_2175_, v___x_2178_);
return v___x_2179_;
}
else
{
lean_dec_ref(v_t_u2081_2175_);
lean_inc_ref(v_t_u2082_2176_);
return v_t_u2082_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2180_, lean_object* v_t_u2082_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2180_, v_t_u2082_2181_);
lean_dec_ref(v_t_u2082_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2183_, lean_object* v_t_u2081_2184_, lean_object* v_t_u2082_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2184_, v_t_u2082_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2187_, lean_object* v_t_u2081_2188_, lean_object* v_t_u2082_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_PersistentArray_append(v_00_u03b1_2187_, v_t_u2081_2188_, v_t_u2082_2189_);
lean_dec_ref(v_t_u2082_2189_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2191_, lean_object* v_t_2192_, lean_object* v_init_2193_, lean_object* v_start_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2192_, v_init_2193_, v_start_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_t_2197_, lean_object* v_init_2198_, lean_object* v_start_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2196_, v_t_2197_, v_init_2198_, v_start_2199_);
lean_dec(v_start_2199_);
lean_dec_ref(v_t_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2201_, lean_object* v_x_2202_, size_t v_x_2203_, size_t v_x_2204_, lean_object* v_x_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2202_, v_x_2203_, v_x_2204_, v_x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
size_t v_x_1679__boxed_2212_; size_t v_x_1680__boxed_2213_; lean_object* v_res_2214_; 
v_x_1679__boxed_2212_ = lean_unbox_usize(v_x_2209_);
lean_dec(v_x_2209_);
v_x_1680__boxed_2213_ = lean_unbox_usize(v_x_2210_);
lean_dec(v_x_2210_);
v_res_2214_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2207_, v_x_2208_, v_x_1679__boxed_2212_, v_x_1680__boxed_2213_, v_x_2211_);
lean_dec_ref(v_x_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2215_, lean_object* v_as_2216_, size_t v_i_2217_, size_t v_stop_2218_, lean_object* v_b_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2216_, v_i_2217_, v_stop_2218_, v_b_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_as_2222_, lean_object* v_i_2223_, lean_object* v_stop_2224_, lean_object* v_b_2225_){
_start:
{
size_t v_i_boxed_2226_; size_t v_stop_boxed_2227_; lean_object* v_res_2228_; 
v_i_boxed_2226_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_stop_boxed_2227_ = lean_unbox_usize(v_stop_2224_);
lean_dec(v_stop_2224_);
v_res_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2221_, v_as_2222_, v_i_boxed_2226_, v_stop_boxed_2227_, v_b_2225_);
lean_dec_ref(v_as_2222_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2230_, v_x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2233_, v_x_2234_, v_x_2235_);
lean_dec_ref(v_x_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2237_, lean_object* v_as_2238_, size_t v_i_2239_, size_t v_stop_2240_, lean_object* v_b_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2238_, v_i_2239_, v_stop_2240_, v_b_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_as_2244_, lean_object* v_i_2245_, lean_object* v_stop_2246_, lean_object* v_b_2247_){
_start:
{
size_t v_i_boxed_2248_; size_t v_stop_boxed_2249_; lean_object* v_res_2250_; 
v_i_boxed_2248_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_stop_boxed_2249_ = lean_unbox_usize(v_stop_2246_);
lean_dec(v_stop_2246_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2243_, v_as_2244_, v_i_boxed_2248_, v_stop_boxed_2249_, v_b_2247_);
lean_dec_ref(v_as_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___closed__0));
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2254_, lean_object* v_x_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_apply_1(v_f_2254_, v_x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2257_, lean_object* v_f_2258_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2262_, lean_object* v_00_u03b2_2263_, lean_object* v_t_2264_, lean_object* v_f_2265_){
_start:
{
lean_object* v___f_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2266_, 0, v_f_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2268_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2267_, v_t_2264_, v___f_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2269_, lean_object* v_f_2270_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2274_, lean_object* v_00_u03b2_2275_, lean_object* v_t_2276_, lean_object* v_f_2277_){
_start:
{
lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2278_, 0, v_f_2277_);
v___x_2279_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2280_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2279_, v_t_2276_, v___f_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2281_, size_t v_i_2282_, size_t v_stop_2283_, lean_object* v_b_2284_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_usize_dec_eq(v_i_2282_, v_stop_2283_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; 
v___x_2286_ = lean_array_uget_borrowed(v_as_2281_, v_i_2282_);
lean_inc(v___x_2286_);
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_b_2284_);
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_add(v_i_2282_, v___x_2288_);
v_i_2282_ = v___x_2289_;
v_b_2284_ = v___x_2287_;
goto _start;
}
else
{
return v_b_2284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2291_, lean_object* v_i_2292_, lean_object* v_stop_2293_, lean_object* v_b_2294_){
_start:
{
size_t v_i_boxed_2295_; size_t v_stop_boxed_2296_; lean_object* v_res_2297_; 
v_i_boxed_2295_ = lean_unbox_usize(v_i_2292_);
lean_dec(v_i_2292_);
v_stop_boxed_2296_ = lean_unbox_usize(v_stop_2293_);
lean_dec(v_stop_2293_);
v_res_2297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2291_, v_i_boxed_2295_, v_stop_boxed_2296_, v_b_2294_);
lean_dec_ref(v_as_2291_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
if (lean_obj_tag(v_x_2298_) == 0)
{
lean_object* v_cs_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_cs_2300_ = lean_ctor_get(v_x_2298_, 0);
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = lean_array_get_size(v_cs_2300_);
v___x_2303_ = lean_nat_dec_lt(v___x_2301_, v___x_2302_);
if (v___x_2303_ == 0)
{
return v_x_2299_;
}
else
{
uint8_t v___x_2304_; 
v___x_2304_ = lean_nat_dec_le(v___x_2302_, v___x_2302_);
if (v___x_2304_ == 0)
{
if (v___x_2303_ == 0)
{
return v_x_2299_;
}
else
{
size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = lean_usize_of_nat(v___x_2302_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2300_, v___x_2305_, v___x_2306_, v_x_2299_);
return v___x_2307_;
}
}
else
{
size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = lean_usize_of_nat(v___x_2302_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2300_, v___x_2308_, v___x_2309_, v_x_2299_);
return v___x_2310_;
}
}
}
else
{
lean_object* v_vs_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_vs_2311_ = lean_ctor_get(v_x_2298_, 0);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_array_get_size(v_vs_2311_);
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
return v_x_2299_;
}
else
{
uint8_t v___x_2315_; 
v___x_2315_ = lean_nat_dec_le(v___x_2313_, v___x_2313_);
if (v___x_2315_ == 0)
{
if (v___x_2314_ == 0)
{
return v_x_2299_;
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = lean_usize_of_nat(v___x_2313_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2311_, v___x_2316_, v___x_2317_, v_x_2299_);
return v___x_2318_;
}
}
else
{
size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = lean_usize_of_nat(v___x_2313_);
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2311_, v___x_2319_, v___x_2320_, v_x_2299_);
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2322_, size_t v_i_2323_, size_t v_stop_2324_, lean_object* v_b_2325_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_eq(v_i_2323_, v_stop_2324_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; 
v___x_2327_ = lean_array_uget_borrowed(v_as_2322_, v_i_2323_);
v___x_2328_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2327_, v_b_2325_);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_i_2323_, v___x_2329_);
v_i_2323_ = v___x_2330_;
v_b_2325_ = v___x_2328_;
goto _start;
}
else
{
return v_b_2325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2332_, lean_object* v_i_2333_, lean_object* v_stop_2334_, lean_object* v_b_2335_){
_start:
{
size_t v_i_boxed_2336_; size_t v_stop_boxed_2337_; lean_object* v_res_2338_; 
v_i_boxed_2336_ = lean_unbox_usize(v_i_2333_);
lean_dec(v_i_2333_);
v_stop_boxed_2337_ = lean_unbox_usize(v_stop_2334_);
lean_dec(v_stop_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2332_, v_i_boxed_2336_, v_stop_boxed_2337_, v_b_2335_);
lean_dec_ref(v_as_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2339_, v_x_2340_);
lean_dec_ref(v_x_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2342_, size_t v_x_2343_, size_t v_x_2344_, lean_object* v_x_2345_){
_start:
{
if (lean_obj_tag(v_x_2342_) == 0)
{
lean_object* v_cs_2346_; lean_object* v___x_2347_; size_t v___x_2348_; lean_object* v_j_2349_; lean_object* v___x_2350_; size_t v___x_2351_; size_t v___x_2352_; size_t v___x_2353_; size_t v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_cs_2346_ = lean_ctor_get(v_x_2342_, 0);
v___x_2347_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2348_ = lean_usize_shift_right(v_x_2343_, v_x_2344_);
v_j_2349_ = lean_usize_to_nat(v___x_2348_);
v___x_2350_ = lean_array_get_borrowed(v___x_2347_, v_cs_2346_, v_j_2349_);
v___x_2351_ = ((size_t)1ULL);
v___x_2352_ = lean_usize_shift_left(v___x_2351_, v_x_2344_);
v___x_2353_ = lean_usize_sub(v___x_2352_, v___x_2351_);
v___x_2354_ = lean_usize_land(v_x_2343_, v___x_2353_);
v___x_2355_ = ((size_t)5ULL);
v___x_2356_ = lean_usize_sub(v_x_2344_, v___x_2355_);
v___x_2357_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2350_, v___x_2354_, v___x_2356_, v_x_2345_);
v___x_2358_ = lean_unsigned_to_nat(1u);
v___x_2359_ = lean_nat_add(v_j_2349_, v___x_2358_);
lean_dec(v_j_2349_);
v___x_2360_ = lean_array_get_size(v_cs_2346_);
v___x_2361_ = lean_nat_dec_lt(v___x_2359_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_dec(v___x_2359_);
return v___x_2357_;
}
else
{
uint8_t v___x_2362_; 
v___x_2362_ = lean_nat_dec_le(v___x_2360_, v___x_2360_);
if (v___x_2362_ == 0)
{
if (v___x_2361_ == 0)
{
lean_dec(v___x_2359_);
return v___x_2357_;
}
else
{
size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_usize_of_nat(v___x_2359_);
lean_dec(v___x_2359_);
v___x_2364_ = lean_usize_of_nat(v___x_2360_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2346_, v___x_2363_, v___x_2364_, v___x_2357_);
return v___x_2365_;
}
}
else
{
size_t v___x_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_usize_of_nat(v___x_2359_);
lean_dec(v___x_2359_);
v___x_2367_ = lean_usize_of_nat(v___x_2360_);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2346_, v___x_2366_, v___x_2367_, v___x_2357_);
return v___x_2368_;
}
}
}
else
{
lean_object* v_vs_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_vs_2369_ = lean_ctor_get(v_x_2342_, 0);
v___x_2370_ = lean_usize_to_nat(v_x_2343_);
v___x_2371_ = lean_array_get_size(v_vs_2369_);
v___x_2372_ = lean_nat_dec_lt(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_dec(v___x_2370_);
return v_x_2345_;
}
else
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_nat_dec_le(v___x_2371_, v___x_2371_);
if (v___x_2373_ == 0)
{
if (v___x_2372_ == 0)
{
lean_dec(v___x_2370_);
return v_x_2345_;
}
else
{
size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_usize_of_nat(v___x_2370_);
lean_dec(v___x_2370_);
v___x_2375_ = lean_usize_of_nat(v___x_2371_);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2369_, v___x_2374_, v___x_2375_, v_x_2345_);
return v___x_2376_;
}
}
else
{
size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_usize_of_nat(v___x_2370_);
lean_dec(v___x_2370_);
v___x_2378_ = lean_usize_of_nat(v___x_2371_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2369_, v___x_2377_, v___x_2378_, v_x_2345_);
return v___x_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
size_t v_x_1497__boxed_2384_; size_t v_x_1498__boxed_2385_; lean_object* v_res_2386_; 
v_x_1497__boxed_2384_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_x_1498__boxed_2385_ = lean_unbox_usize(v_x_2382_);
lean_dec(v_x_2382_);
v_res_2386_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2380_, v_x_1497__boxed_2384_, v_x_1498__boxed_2385_, v_x_2383_);
lean_dec_ref(v_x_2380_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2387_, lean_object* v_init_2388_, lean_object* v_start_2389_){
_start:
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = lean_nat_dec_eq(v_start_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v_root_2392_; lean_object* v_tail_2393_; size_t v_shift_2394_; lean_object* v_tailOff_2395_; uint8_t v___x_2396_; 
v_root_2392_ = lean_ctor_get(v_t_2387_, 0);
v_tail_2393_ = lean_ctor_get(v_t_2387_, 1);
v_shift_2394_ = lean_ctor_get_usize(v_t_2387_, 4);
v_tailOff_2395_ = lean_ctor_get(v_t_2387_, 3);
v___x_2396_ = lean_nat_dec_le(v_tailOff_2395_, v_start_2389_);
if (v___x_2396_ == 0)
{
size_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2397_ = lean_usize_of_nat(v_start_2389_);
v___x_2398_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2392_, v___x_2397_, v_shift_2394_, v_init_2388_);
v___x_2399_ = lean_array_get_size(v_tail_2393_);
v___x_2400_ = lean_nat_dec_lt(v___x_2390_, v___x_2399_);
if (v___x_2400_ == 0)
{
return v___x_2398_;
}
else
{
uint8_t v___x_2401_; 
v___x_2401_ = lean_nat_dec_le(v___x_2399_, v___x_2399_);
if (v___x_2401_ == 0)
{
if (v___x_2400_ == 0)
{
return v___x_2398_;
}
else
{
size_t v___x_2402_; size_t v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((size_t)0ULL);
v___x_2403_ = lean_usize_of_nat(v___x_2399_);
v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2393_, v___x_2402_, v___x_2403_, v___x_2398_);
return v___x_2404_;
}
}
else
{
size_t v___x_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = lean_usize_of_nat(v___x_2399_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2393_, v___x_2405_, v___x_2406_, v___x_2398_);
return v___x_2407_;
}
}
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2408_ = lean_nat_sub(v_start_2389_, v_tailOff_2395_);
v___x_2409_ = lean_array_get_size(v_tail_2393_);
v___x_2410_ = lean_nat_dec_lt(v___x_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_dec(v___x_2408_);
return v_init_2388_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_nat_dec_le(v___x_2409_, v___x_2409_);
if (v___x_2411_ == 0)
{
if (v___x_2410_ == 0)
{
lean_dec(v___x_2408_);
return v_init_2388_;
}
else
{
size_t v___x_2412_; size_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_usize_of_nat(v___x_2408_);
lean_dec(v___x_2408_);
v___x_2413_ = lean_usize_of_nat(v___x_2409_);
v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2393_, v___x_2412_, v___x_2413_, v_init_2388_);
return v___x_2414_;
}
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_usize_of_nat(v___x_2408_);
lean_dec(v___x_2408_);
v___x_2416_ = lean_usize_of_nat(v___x_2409_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2393_, v___x_2415_, v___x_2416_, v_init_2388_);
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_root_2418_; lean_object* v_tail_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v_root_2418_ = lean_ctor_get(v_t_2387_, 0);
v_tail_2419_ = lean_ctor_get(v_t_2387_, 1);
v___x_2420_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2418_, v_init_2388_);
v___x_2421_ = lean_array_get_size(v_tail_2419_);
v___x_2422_ = lean_nat_dec_lt(v___x_2390_, v___x_2421_);
if (v___x_2422_ == 0)
{
return v___x_2420_;
}
else
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
if (v___x_2423_ == 0)
{
if (v___x_2422_ == 0)
{
return v___x_2420_;
}
else
{
size_t v___x_2424_; size_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = lean_usize_of_nat(v___x_2421_);
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2419_, v___x_2424_, v___x_2425_, v___x_2420_);
return v___x_2426_;
}
}
else
{
size_t v___x_2427_; size_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = ((size_t)0ULL);
v___x_2428_ = lean_usize_of_nat(v___x_2421_);
v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2419_, v___x_2427_, v___x_2428_, v___x_2420_);
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2430_, lean_object* v_init_2431_, lean_object* v_start_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2430_, v_init_2431_, v_start_2432_);
lean_dec(v_start_2432_);
lean_dec_ref(v_t_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2434_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2434_, v___x_2435_, v___x_2436_);
v___x_2438_ = l_List_reverse___redArg(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_PersistentArray_toList___redArg(v_t_2439_);
lean_dec_ref(v_t_2439_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2441_, lean_object* v_t_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_PersistentArray_toList___redArg(v_t_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_t_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_PersistentArray_toList(v_00_u03b1_2444_, v_t_2445_);
lean_dec_ref(v_t_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2447_, lean_object* v_t_2448_, lean_object* v_init_2449_, lean_object* v_start_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2448_, v_init_2449_, v_start_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_t_2453_, lean_object* v_init_2454_, lean_object* v_start_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2452_, v_t_2453_, v_init_2454_, v_start_2455_);
lean_dec(v_start_2455_);
lean_dec_ref(v_t_2453_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2457_, lean_object* v_x_2458_, size_t v_x_2459_, size_t v_x_2460_, lean_object* v_x_2461_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2458_, v_x_2459_, v_x_2460_, v_x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
size_t v_x_1655__boxed_2468_; size_t v_x_1656__boxed_2469_; lean_object* v_res_2470_; 
v_x_1655__boxed_2468_ = lean_unbox_usize(v_x_2465_);
lean_dec(v_x_2465_);
v_x_1656__boxed_2469_ = lean_unbox_usize(v_x_2466_);
lean_dec(v_x_2466_);
v_res_2470_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2463_, v_x_2464_, v_x_1655__boxed_2468_, v_x_1656__boxed_2469_, v_x_2467_);
lean_dec_ref(v_x_2464_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2471_, lean_object* v_as_2472_, size_t v_i_2473_, size_t v_stop_2474_, lean_object* v_b_2475_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2472_, v_i_2473_, v_stop_2474_, v_b_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2477_, lean_object* v_as_2478_, lean_object* v_i_2479_, lean_object* v_stop_2480_, lean_object* v_b_2481_){
_start:
{
size_t v_i_boxed_2482_; size_t v_stop_boxed_2483_; lean_object* v_res_2484_; 
v_i_boxed_2482_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_stop_boxed_2483_ = lean_unbox_usize(v_stop_2480_);
lean_dec(v_stop_2480_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2477_, v_as_2478_, v_i_boxed_2482_, v_stop_boxed_2483_, v_b_2481_);
lean_dec_ref(v_as_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2486_, v_x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2489_, v_x_2490_, v_x_2491_);
lean_dec_ref(v_x_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2493_, lean_object* v_as_2494_, size_t v_i_2495_, size_t v_stop_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2494_, v_i_2495_, v_stop_2496_, v_b_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_stop_2502_, lean_object* v_b_2503_){
_start:
{
size_t v_i_boxed_2504_; size_t v_stop_boxed_2505_; lean_object* v_res_2506_; 
v_i_boxed_2504_ = lean_unbox_usize(v_i_2501_);
lean_dec(v_i_2501_);
v_stop_boxed_2505_ = lean_unbox_usize(v_stop_2502_);
lean_dec(v_stop_2502_);
v_res_2506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2499_, v_as_2500_, v_i_boxed_2504_, v_stop_boxed_2505_, v_b_2503_);
lean_dec_ref(v_as_2500_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2507_, lean_object* v_p_2508_, lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
lean_object* v_cs_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_cs_2510_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_cs_2510_);
lean_dec_ref(v_x_2509_);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_array_get_size(v_cs_2510_);
v___x_2513_ = lean_nat_dec_lt(v___x_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v_toApplicative_2514_; lean_object* v_toPure_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_dec_ref(v_cs_2510_);
lean_dec(v_p_2508_);
v_toApplicative_2514_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc_ref(v_toApplicative_2514_);
lean_dec_ref(v_inst_2507_);
v_toPure_2515_ = lean_ctor_get(v_toApplicative_2514_, 1);
lean_inc(v_toPure_2515_);
lean_dec_ref(v_toApplicative_2514_);
v___x_2516_ = lean_box(v___x_2513_);
v___x_2517_ = lean_apply_2(v_toPure_2515_, lean_box(0), v___x_2516_);
return v___x_2517_;
}
else
{
if (v___x_2513_ == 0)
{
lean_object* v_toApplicative_2518_; lean_object* v_toPure_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v_cs_2510_);
lean_dec(v_p_2508_);
v_toApplicative_2518_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc_ref(v_toApplicative_2518_);
lean_dec_ref(v_inst_2507_);
v_toPure_2519_ = lean_ctor_get(v_toApplicative_2518_, 1);
lean_inc(v_toPure_2519_);
lean_dec_ref(v_toApplicative_2518_);
v___x_2520_ = lean_box(v___x_2513_);
v___x_2521_ = lean_apply_2(v_toPure_2519_, lean_box(0), v___x_2520_);
return v___x_2521_;
}
else
{
lean_object* v___f_2522_; size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
lean_inc_ref(v_inst_2507_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2522_, 0, v_inst_2507_);
lean_closure_set(v___f_2522_, 1, v_p_2508_);
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2512_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2507_, v___f_2522_, v_cs_2510_, v___x_2523_, v___x_2524_);
return v___x_2525_;
}
}
}
else
{
lean_object* v_vs_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_vs_2526_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_ref(v_vs_2526_);
lean_dec_ref(v_x_2509_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_array_get_size(v_vs_2526_);
v___x_2529_ = lean_nat_dec_lt(v___x_2527_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v_toApplicative_2530_; lean_object* v_toPure_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec_ref(v_vs_2526_);
lean_dec(v_p_2508_);
v_toApplicative_2530_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc_ref(v_toApplicative_2530_);
lean_dec_ref(v_inst_2507_);
v_toPure_2531_ = lean_ctor_get(v_toApplicative_2530_, 1);
lean_inc(v_toPure_2531_);
lean_dec_ref(v_toApplicative_2530_);
v___x_2532_ = lean_box(v___x_2529_);
v___x_2533_ = lean_apply_2(v_toPure_2531_, lean_box(0), v___x_2532_);
return v___x_2533_;
}
else
{
if (v___x_2529_ == 0)
{
lean_object* v_toApplicative_2534_; lean_object* v_toPure_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v_vs_2526_);
lean_dec(v_p_2508_);
v_toApplicative_2534_ = lean_ctor_get(v_inst_2507_, 0);
lean_inc_ref(v_toApplicative_2534_);
lean_dec_ref(v_inst_2507_);
v_toPure_2535_ = lean_ctor_get(v_toApplicative_2534_, 1);
lean_inc(v_toPure_2535_);
lean_dec_ref(v_toApplicative_2534_);
v___x_2536_ = lean_box(v___x_2529_);
v___x_2537_ = lean_apply_2(v_toPure_2535_, lean_box(0), v___x_2536_);
return v___x_2537_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = lean_usize_of_nat(v___x_2528_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2507_, v_p_2508_, v_vs_2526_, v___x_2538_, v___x_2539_);
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2541_, lean_object* v_p_2542_, lean_object* v_c_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2541_, v_p_2542_, v_c_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2545_, lean_object* v_m_2546_, lean_object* v_inst_2547_, lean_object* v_p_2548_, lean_object* v_x_2549_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2547_, v_p_2548_, v_x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2551_, lean_object* v_toPure_2552_, lean_object* v_inst_2553_, lean_object* v_p_2554_, uint8_t v_b_2555_){
_start:
{
if (v_b_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = lean_array_get_size(v_tail_2551_);
v___x_2558_ = lean_nat_dec_lt(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v_p_2554_);
lean_dec_ref(v_inst_2553_);
lean_dec_ref(v_tail_2551_);
v___x_2559_ = lean_box(v_b_2555_);
v___x_2560_ = lean_apply_2(v_toPure_2552_, lean_box(0), v___x_2559_);
return v___x_2560_;
}
else
{
if (v___x_2558_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v_p_2554_);
lean_dec_ref(v_inst_2553_);
lean_dec_ref(v_tail_2551_);
v___x_2561_ = lean_box(v_b_2555_);
v___x_2562_ = lean_apply_2(v_toPure_2552_, lean_box(0), v___x_2561_);
return v___x_2562_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_toPure_2552_);
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2557_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2553_, v_p_2554_, v_tail_2551_, v___x_2563_, v___x_2564_);
return v___x_2565_;
}
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_p_2554_);
lean_dec_ref(v_inst_2553_);
lean_dec_ref(v_tail_2551_);
v___x_2566_ = lean_box(v_b_2555_);
v___x_2567_ = lean_apply_2(v_toPure_2552_, lean_box(0), v___x_2566_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2568_, lean_object* v_toPure_2569_, lean_object* v_inst_2570_, lean_object* v_p_2571_, lean_object* v_b_2572_){
_start:
{
uint8_t v_b_boxed_2573_; lean_object* v_res_2574_; 
v_b_boxed_2573_ = lean_unbox(v_b_2572_);
v_res_2574_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2568_, v_toPure_2569_, v_inst_2570_, v_p_2571_, v_b_boxed_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2575_, lean_object* v_t_2576_, lean_object* v_p_2577_){
_start:
{
lean_object* v_toApplicative_2578_; lean_object* v_toBind_2579_; lean_object* v_root_2580_; lean_object* v_tail_2581_; lean_object* v_toPure_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; 
v_toApplicative_2578_ = lean_ctor_get(v_inst_2575_, 0);
v_toBind_2579_ = lean_ctor_get(v_inst_2575_, 1);
lean_inc(v_toBind_2579_);
v_root_2580_ = lean_ctor_get(v_t_2576_, 0);
lean_inc_ref(v_root_2580_);
v_tail_2581_ = lean_ctor_get(v_t_2576_, 1);
lean_inc_ref(v_tail_2581_);
lean_dec_ref(v_t_2576_);
v_toPure_2582_ = lean_ctor_get(v_toApplicative_2578_, 1);
lean_inc(v_toPure_2582_);
lean_inc(v_p_2577_);
lean_inc_ref(v_inst_2575_);
v___x_2583_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2575_, v_p_2577_, v_root_2580_);
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2584_, 0, v_tail_2581_);
lean_closure_set(v___f_2584_, 1, v_toPure_2582_);
lean_closure_set(v___f_2584_, 2, v_inst_2575_);
lean_closure_set(v___f_2584_, 3, v_p_2577_);
v___x_2585_ = lean_apply_4(v_toBind_2579_, lean_box(0), lean_box(0), v___x_2583_, v___f_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2586_, lean_object* v_m_2587_, lean_object* v_inst_2588_, lean_object* v_t_2589_, lean_object* v_p_2590_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2588_, v_t_2589_, v_p_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2592_, uint8_t v_b_2593_){
_start:
{
if (v_b_2593_ == 0)
{
uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = 1;
v___x_2595_ = lean_box(v___x_2594_);
v___x_2596_ = lean_apply_2(v_toPure_2592_, lean_box(0), v___x_2595_);
return v___x_2596_;
}
else
{
uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = 0;
v___x_2598_ = lean_box(v___x_2597_);
v___x_2599_ = lean_apply_2(v_toPure_2592_, lean_box(0), v___x_2598_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2600_, lean_object* v_b_2601_){
_start:
{
uint8_t v_b_boxed_2602_; lean_object* v_res_2603_; 
v_b_boxed_2602_ = lean_unbox(v_b_2601_);
v_res_2603_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2600_, v_b_boxed_2602_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2604_, lean_object* v_toBind_2605_, lean_object* v___f_2606_, lean_object* v_v_2607_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_apply_1(v_p_2604_, v_v_2607_);
v___x_2609_ = lean_apply_4(v_toBind_2605_, lean_box(0), lean_box(0), v___x_2608_, v___f_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2610_, lean_object* v_a_2611_, lean_object* v_p_2612_){
_start:
{
lean_object* v_toApplicative_2613_; lean_object* v_toBind_2614_; lean_object* v_toPure_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_toApplicative_2613_ = lean_ctor_get(v_inst_2610_, 0);
v_toBind_2614_ = lean_ctor_get(v_inst_2610_, 1);
lean_inc_n(v_toBind_2614_, 2);
v_toPure_2615_ = lean_ctor_get(v_toApplicative_2613_, 1);
lean_inc(v_toPure_2615_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2616_, 0, v_toPure_2615_);
lean_inc_ref(v___f_2616_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2617_, 0, v_p_2612_);
lean_closure_set(v___f_2617_, 1, v_toBind_2614_);
lean_closure_set(v___f_2617_, 2, v___f_2616_);
v___x_2618_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2610_, v_a_2611_, v___f_2617_);
v___x_2619_ = lean_apply_4(v_toBind_2614_, lean_box(0), lean_box(0), v___x_2618_, v___f_2616_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2620_, lean_object* v_m_2621_, lean_object* v_inst_2622_, lean_object* v_a_2623_, lean_object* v_p_2624_){
_start:
{
lean_object* v_toApplicative_2625_; lean_object* v_toBind_2626_; lean_object* v_toPure_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v_toApplicative_2625_ = lean_ctor_get(v_inst_2622_, 0);
v_toBind_2626_ = lean_ctor_get(v_inst_2622_, 1);
lean_inc_n(v_toBind_2626_, 2);
v_toPure_2627_ = lean_ctor_get(v_toApplicative_2625_, 1);
lean_inc(v_toPure_2627_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2628_, 0, v_toPure_2627_);
lean_inc_ref(v___f_2628_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2629_, 0, v_p_2624_);
lean_closure_set(v___f_2629_, 1, v_toBind_2626_);
lean_closure_set(v___f_2629_, 2, v___f_2628_);
v___x_2630_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2622_, v_a_2623_, v___f_2629_);
v___x_2631_ = lean_apply_4(v_toBind_2626_, lean_box(0), lean_box(0), v___x_2630_, v___f_2628_);
return v___x_2631_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2632_, lean_object* v_x_2633_){
_start:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_apply_1(v_p_2632_, v_x_2633_);
v___x_2635_ = lean_unbox(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2636_, lean_object* v_x_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2636_, v_x_2637_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg(lean_object* v_a_2640_, lean_object* v_p_2641_){
_start:
{
lean_object* v___f_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2642_, 0, v_p_2641_);
v___x_2643_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2644_ = l_Lean_PersistentArray_anyM___redArg(v___x_2643_, v_a_2640_, v___f_2642_);
v___x_2645_ = lean_unbox(v___x_2644_);
lean_dec(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___boxed(lean_object* v_a_2646_, lean_object* v_p_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l_Lean_PersistentArray_any___redArg(v_a_2646_, v_p_2647_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2650_, lean_object* v_a_2651_, lean_object* v_p_2652_){
_start:
{
lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___f_2653_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2653_, 0, v_p_2652_);
v___x_2654_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2655_ = l_Lean_PersistentArray_anyM___redArg(v___x_2654_, v_a_2651_, v___f_2653_);
v___x_2656_ = lean_unbox(v___x_2655_);
lean_dec(v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2657_, lean_object* v_a_2658_, lean_object* v_p_2659_){
_start:
{
uint8_t v_res_2660_; lean_object* v_r_2661_; 
v_res_2660_ = l_Lean_PersistentArray_any(v_00_u03b1_2657_, v_a_2658_, v_p_2659_);
v_r_2661_ = lean_box(v_res_2660_);
return v_r_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = lean_apply_1(v_p_2662_, v_x_2663_);
v___x_2665_ = lean_unbox(v___x_2664_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; 
v___x_2666_ = 1;
return v___x_2666_;
}
else
{
uint8_t v___x_2667_; 
v___x_2667_ = 0;
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2668_, lean_object* v_x_2669_){
_start:
{
uint8_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2668_, v_x_2669_);
v_r_2671_ = lean_box(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2672_, lean_object* v_p_2673_){
_start:
{
lean_object* v___f_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___f_2674_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2674_, 0, v_p_2673_);
v___x_2675_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2676_ = l_Lean_PersistentArray_anyM___redArg(v___x_2675_, v_a_2672_, v___f_2674_);
v___x_2677_ = lean_unbox(v___x_2676_);
lean_dec(v___x_2676_);
if (v___x_2677_ == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = 1;
return v___x_2678_;
}
else
{
uint8_t v___x_2679_; 
v___x_2679_ = 0;
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2680_, lean_object* v_p_2681_){
_start:
{
uint8_t v_res_2682_; lean_object* v_r_2683_; 
v_res_2682_ = l_Lean_PersistentArray_all___redArg(v_a_2680_, v_p_2681_);
v_r_2683_ = lean_box(v_res_2682_);
return v_r_2683_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2684_, lean_object* v_a_2685_, lean_object* v_p_2686_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___f_2687_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2687_, 0, v_p_2686_);
v___x_2688_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2689_ = l_Lean_PersistentArray_anyM___redArg(v___x_2688_, v_a_2685_, v___f_2687_);
v___x_2690_ = lean_unbox(v___x_2689_);
lean_dec(v___x_2689_);
if (v___x_2690_ == 0)
{
uint8_t v___x_2691_; 
v___x_2691_ = 1;
return v___x_2691_;
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2693_, lean_object* v_a_2694_, lean_object* v_p_2695_){
_start:
{
uint8_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = l_Lean_PersistentArray_all(v_00_u03b1_2693_, v_a_2694_, v_p_2695_);
v_r_2697_ = lean_box(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2698_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_cs_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_vs_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2704_, lean_object* v_f_2705_, lean_object* v_x_2706_){
_start:
{
if (lean_obj_tag(v_x_2706_) == 0)
{
lean_object* v_toApplicative_2707_; lean_object* v_toFunctor_2708_; lean_object* v_cs_2709_; lean_object* v_map_2710_; lean_object* v___f_2711_; lean_object* v___f_2712_; size_t v_sz_2713_; size_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_toApplicative_2707_ = lean_ctor_get(v_inst_2704_, 0);
v_toFunctor_2708_ = lean_ctor_get(v_toApplicative_2707_, 0);
v_cs_2709_ = lean_ctor_get(v_x_2706_, 0);
lean_inc_ref(v_cs_2709_);
lean_dec_ref(v_x_2706_);
v_map_2710_ = lean_ctor_get(v_toFunctor_2708_, 0);
lean_inc(v_map_2710_);
v___f_2711_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2704_);
v___f_2712_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2712_, 0, v_inst_2704_);
lean_closure_set(v___f_2712_, 1, v_f_2705_);
v_sz_2713_ = lean_array_size(v_cs_2709_);
v___x_2714_ = ((size_t)0ULL);
v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2704_, v___f_2712_, v_sz_2713_, v___x_2714_, v_cs_2709_);
v___x_2716_ = lean_apply_4(v_map_2710_, lean_box(0), lean_box(0), v___f_2711_, v___x_2715_);
return v___x_2716_;
}
else
{
lean_object* v_toApplicative_2717_; lean_object* v_toFunctor_2718_; lean_object* v_vs_2719_; lean_object* v_map_2720_; lean_object* v___f_2721_; size_t v_sz_2722_; size_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_toApplicative_2717_ = lean_ctor_get(v_inst_2704_, 0);
v_toFunctor_2718_ = lean_ctor_get(v_toApplicative_2717_, 0);
v_vs_2719_ = lean_ctor_get(v_x_2706_, 0);
lean_inc_ref(v_vs_2719_);
lean_dec_ref(v_x_2706_);
v_map_2720_ = lean_ctor_get(v_toFunctor_2718_, 0);
lean_inc(v_map_2720_);
v___f_2721_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2722_ = lean_array_size(v_vs_2719_);
v___x_2723_ = ((size_t)0ULL);
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2704_, v_f_2705_, v_sz_2722_, v___x_2723_, v_vs_2719_);
v___x_2725_ = lean_apply_4(v_map_2720_, lean_box(0), lean_box(0), v___f_2721_, v___x_2724_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2726_, lean_object* v_f_2727_, lean_object* v_c_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2726_, v_f_2727_, v_c_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2730_, lean_object* v_m_2731_, lean_object* v_inst_2732_, lean_object* v_00_u03b2_2733_, lean_object* v_f_2734_, lean_object* v_x_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2732_, v_f_2734_, v_x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2737_, lean_object* v_size_2738_, size_t v_shift_2739_, lean_object* v_tailOff_2740_, lean_object* v_toPure_2741_, lean_object* v_tail_2742_){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2743_, 0, v_root_2737_);
lean_ctor_set(v___x_2743_, 1, v_tail_2742_);
lean_ctor_set(v___x_2743_, 2, v_size_2738_);
lean_ctor_set(v___x_2743_, 3, v_tailOff_2740_);
lean_ctor_set_usize(v___x_2743_, 4, v_shift_2739_);
v___x_2744_ = lean_apply_2(v_toPure_2741_, lean_box(0), v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2745_, lean_object* v_size_2746_, lean_object* v_shift_2747_, lean_object* v_tailOff_2748_, lean_object* v_toPure_2749_, lean_object* v_tail_2750_){
_start:
{
size_t v_shift_boxed_2751_; lean_object* v_res_2752_; 
v_shift_boxed_2751_ = lean_unbox_usize(v_shift_2747_);
lean_dec(v_shift_2747_);
v_res_2752_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2745_, v_size_2746_, v_shift_boxed_2751_, v_tailOff_2748_, v_toPure_2749_, v_tail_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2753_, size_t v_shift_2754_, lean_object* v_tailOff_2755_, lean_object* v_toPure_2756_, lean_object* v_tail_2757_, lean_object* v_inst_2758_, lean_object* v_f_2759_, lean_object* v_toBind_2760_, lean_object* v_root_2761_){
_start:
{
lean_object* v___x_2762_; lean_object* v___f_2763_; size_t v_sz_2764_; size_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2762_ = lean_box_usize(v_shift_2754_);
v___f_2763_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2763_, 0, v_root_2761_);
lean_closure_set(v___f_2763_, 1, v_size_2753_);
lean_closure_set(v___f_2763_, 2, v___x_2762_);
lean_closure_set(v___f_2763_, 3, v_tailOff_2755_);
lean_closure_set(v___f_2763_, 4, v_toPure_2756_);
v_sz_2764_ = lean_array_size(v_tail_2757_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2758_, v_f_2759_, v_sz_2764_, v___x_2765_, v_tail_2757_);
v___x_2767_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v___x_2766_, v___f_2763_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2768_, lean_object* v_shift_2769_, lean_object* v_tailOff_2770_, lean_object* v_toPure_2771_, lean_object* v_tail_2772_, lean_object* v_inst_2773_, lean_object* v_f_2774_, lean_object* v_toBind_2775_, lean_object* v_root_2776_){
_start:
{
size_t v_shift_boxed_2777_; lean_object* v_res_2778_; 
v_shift_boxed_2777_ = lean_unbox_usize(v_shift_2769_);
lean_dec(v_shift_2769_);
v_res_2778_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2768_, v_shift_boxed_2777_, v_tailOff_2770_, v_toPure_2771_, v_tail_2772_, v_inst_2773_, v_f_2774_, v_toBind_2775_, v_root_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2779_, lean_object* v_f_2780_, lean_object* v_t_2781_){
_start:
{
lean_object* v_toApplicative_2782_; lean_object* v_toBind_2783_; lean_object* v_root_2784_; lean_object* v_tail_2785_; lean_object* v_size_2786_; size_t v_shift_2787_; lean_object* v_tailOff_2788_; lean_object* v_toPure_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; 
v_toApplicative_2782_ = lean_ctor_get(v_inst_2779_, 0);
v_toBind_2783_ = lean_ctor_get(v_inst_2779_, 1);
lean_inc_n(v_toBind_2783_, 2);
v_root_2784_ = lean_ctor_get(v_t_2781_, 0);
lean_inc_ref(v_root_2784_);
v_tail_2785_ = lean_ctor_get(v_t_2781_, 1);
lean_inc_ref(v_tail_2785_);
v_size_2786_ = lean_ctor_get(v_t_2781_, 2);
lean_inc(v_size_2786_);
v_shift_2787_ = lean_ctor_get_usize(v_t_2781_, 4);
v_tailOff_2788_ = lean_ctor_get(v_t_2781_, 3);
lean_inc(v_tailOff_2788_);
lean_dec_ref(v_t_2781_);
v_toPure_2789_ = lean_ctor_get(v_toApplicative_2782_, 1);
lean_inc(v_toPure_2789_);
lean_inc(v_f_2780_);
lean_inc_ref(v_inst_2779_);
v___x_2790_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2779_, v_f_2780_, v_root_2784_);
v___x_2791_ = lean_box_usize(v_shift_2787_);
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2792_, 0, v_size_2786_);
lean_closure_set(v___f_2792_, 1, v___x_2791_);
lean_closure_set(v___f_2792_, 2, v_tailOff_2788_);
lean_closure_set(v___f_2792_, 3, v_toPure_2789_);
lean_closure_set(v___f_2792_, 4, v_tail_2785_);
lean_closure_set(v___f_2792_, 5, v_inst_2779_);
lean_closure_set(v___f_2792_, 6, v_f_2780_);
lean_closure_set(v___f_2792_, 7, v_toBind_2783_);
v___x_2793_ = lean_apply_4(v_toBind_2783_, lean_box(0), lean_box(0), v___x_2790_, v___f_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2794_, lean_object* v_m_2795_, lean_object* v_inst_2796_, lean_object* v_00_u03b2_2797_, lean_object* v_f_2798_, lean_object* v_t_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2796_, v_f_2798_, v_t_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_apply_1(v_f_2801_, v_x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2804_, lean_object* v_t_2805_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2809_, lean_object* v_00_u03b2_2810_, lean_object* v_f_2811_, lean_object* v_t_2812_){
_start:
{
lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2813_, 0, v_f_2811_);
v___x_2814_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2815_ = l_Lean_PersistentArray_mapM___redArg(v___x_2814_, v___f_2813_, v_t_2812_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
if (lean_obj_tag(v_x_2816_) == 0)
{
lean_object* v_cs_2819_; lean_object* v_numNodes_2820_; lean_object* v_depth_2821_; lean_object* v_tailSize_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2844_; 
v_cs_2819_ = lean_ctor_get(v_x_2816_, 0);
v_numNodes_2820_ = lean_ctor_get(v_x_2817_, 0);
v_depth_2821_ = lean_ctor_get(v_x_2817_, 1);
v_tailSize_2822_ = lean_ctor_get(v_x_2817_, 2);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2824_ = v_x_2817_;
v_isShared_2825_ = v_isSharedCheck_2844_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_tailSize_2822_);
lean_inc(v_depth_2821_);
lean_inc(v_numNodes_2820_);
lean_dec(v_x_2817_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2844_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___y_2829_; uint8_t v___x_2843_; 
v___x_2826_ = lean_unsigned_to_nat(1u);
v___x_2827_ = lean_nat_add(v_numNodes_2820_, v___x_2826_);
lean_dec(v_numNodes_2820_);
v___x_2843_ = lean_nat_dec_le(v_x_2818_, v_depth_2821_);
if (v___x_2843_ == 0)
{
lean_dec(v_depth_2821_);
lean_inc(v_x_2818_);
v___y_2829_ = v_x_2818_;
goto v___jp_2828_;
}
else
{
v___y_2829_ = v_depth_2821_;
goto v___jp_2828_;
}
v___jp_2828_:
{
lean_object* v___x_2831_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 1, v___y_2829_);
lean_ctor_set(v___x_2824_, 0, v___x_2827_);
v___x_2831_ = v___x_2824_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___y_2829_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_tailSize_2822_);
v___x_2831_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = lean_array_get_size(v_cs_2819_);
v___x_2834_ = lean_nat_dec_lt(v___x_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_dec(v_x_2818_);
return v___x_2831_;
}
else
{
uint8_t v___x_2835_; 
v___x_2835_ = lean_nat_dec_le(v___x_2833_, v___x_2833_);
if (v___x_2835_ == 0)
{
if (v___x_2834_ == 0)
{
lean_dec(v_x_2818_);
return v___x_2831_;
}
else
{
size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = lean_usize_of_nat(v___x_2833_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2818_, v_cs_2819_, v___x_2836_, v___x_2837_, v___x_2831_);
lean_dec(v_x_2818_);
return v___x_2838_;
}
}
else
{
size_t v___x_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = ((size_t)0ULL);
v___x_2840_ = lean_usize_of_nat(v___x_2833_);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2818_, v_cs_2819_, v___x_2839_, v___x_2840_, v___x_2831_);
lean_dec(v_x_2818_);
return v___x_2841_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2845_; lean_object* v_depth_2846_; lean_object* v_tailSize_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2860_; 
v_numNodes_2845_ = lean_ctor_get(v_x_2817_, 0);
v_depth_2846_ = lean_ctor_get(v_x_2817_, 1);
v_tailSize_2847_ = lean_ctor_get(v_x_2817_, 2);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2849_ = v_x_2817_;
v_isShared_2850_ = v_isSharedCheck_2860_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_tailSize_2847_);
lean_inc(v_depth_2846_);
lean_inc(v_numNodes_2845_);
lean_dec(v_x_2817_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2860_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2851_ = lean_unsigned_to_nat(1u);
v___x_2852_ = lean_nat_add(v_numNodes_2845_, v___x_2851_);
lean_dec(v_numNodes_2845_);
v___x_2853_ = lean_nat_dec_le(v_x_2818_, v_depth_2846_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v_depth_2846_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_x_2818_);
lean_ctor_set(v___x_2849_, 0, v___x_2852_);
v___x_2855_ = v___x_2849_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_x_2818_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_tailSize_2847_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v_x_2818_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2852_);
v___x_2858_ = v___x_2849_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_depth_2846_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_tailSize_2847_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2861_, lean_object* v_as_2862_, size_t v_i_2863_, size_t v_stop_2864_, lean_object* v_b_2865_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_usize_dec_eq(v_i_2863_, v_stop_2864_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; size_t v___x_2871_; size_t v___x_2872_; 
v___x_2867_ = lean_array_uget_borrowed(v_as_2862_, v_i_2863_);
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_add(v_x_2861_, v___x_2868_);
v___x_2870_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2867_, v_b_2865_, v___x_2869_);
v___x_2871_ = ((size_t)1ULL);
v___x_2872_ = lean_usize_add(v_i_2863_, v___x_2871_);
v_i_2863_ = v___x_2872_;
v_b_2865_ = v___x_2870_;
goto _start;
}
else
{
return v_b_2865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2874_, lean_object* v_as_2875_, lean_object* v_i_2876_, lean_object* v_stop_2877_, lean_object* v_b_2878_){
_start:
{
size_t v_i_boxed_2879_; size_t v_stop_boxed_2880_; lean_object* v_res_2881_; 
v_i_boxed_2879_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_stop_boxed_2880_ = lean_unbox_usize(v_stop_2877_);
lean_dec(v_stop_2877_);
v_res_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2874_, v_as_2875_, v_i_boxed_2879_, v_stop_boxed_2880_, v_b_2878_);
lean_dec_ref(v_as_2875_);
lean_dec(v_x_2874_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2882_, v_x_2883_, v_x_2884_);
lean_dec_ref(v_x_2882_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2887_, v_x_2888_, v_x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2891_, v_x_2892_, v_x_2893_, v_x_2894_);
lean_dec_ref(v_x_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2896_, lean_object* v_x_2897_, lean_object* v_as_2898_, size_t v_i_2899_, size_t v_stop_2900_, lean_object* v_b_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2897_, v_as_2898_, v_i_2899_, v_stop_2900_, v_b_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2903_, lean_object* v_x_2904_, lean_object* v_as_2905_, lean_object* v_i_2906_, lean_object* v_stop_2907_, lean_object* v_b_2908_){
_start:
{
size_t v_i_boxed_2909_; size_t v_stop_boxed_2910_; lean_object* v_res_2911_; 
v_i_boxed_2909_ = lean_unbox_usize(v_i_2906_);
lean_dec(v_i_2906_);
v_stop_boxed_2910_ = lean_unbox_usize(v_stop_2907_);
lean_dec(v_stop_2907_);
v_res_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2903_, v_x_2904_, v_as_2905_, v_i_boxed_2909_, v_stop_boxed_2910_, v_b_2908_);
lean_dec_ref(v_as_2905_);
lean_dec(v_x_2904_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2912_){
_start:
{
lean_object* v_root_2913_; lean_object* v_tail_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_root_2913_ = lean_ctor_get(v_r_2912_, 0);
v_tail_2914_ = lean_ctor_get(v_r_2912_, 1);
v___x_2915_ = lean_unsigned_to_nat(0u);
v___x_2916_ = lean_array_get_size(v_tail_2914_);
v___x_2917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set(v___x_2917_, 1, v___x_2915_);
lean_ctor_set(v___x_2917_, 2, v___x_2916_);
v___x_2918_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2913_, v___x_2917_, v___x_2915_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_PersistentArray_stats___redArg(v_r_2919_);
lean_dec_ref(v_r_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2921_, lean_object* v_r_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_PersistentArray_stats___redArg(v_r_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_r_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_PersistentArray_stats(v_00_u03b1_2924_, v_r_2925_);
lean_dec_ref(v_r_2925_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2931_){
_start:
{
lean_object* v_numNodes_2932_; lean_object* v_depth_2933_; lean_object* v_tailSize_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_numNodes_2932_ = lean_ctor_get(v_s_2931_, 0);
lean_inc(v_numNodes_2932_);
v_depth_2933_ = lean_ctor_get(v_s_2931_, 1);
lean_inc(v_depth_2933_);
v_tailSize_2934_ = lean_ctor_get(v_s_2931_, 2);
lean_inc(v_tailSize_2934_);
lean_dec_ref(v_s_2931_);
v___x_2935_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2936_ = l_Nat_reprFast(v_numNodes_2932_);
v___x_2937_ = lean_string_append(v___x_2935_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2939_ = lean_string_append(v___x_2937_, v___x_2938_);
v___x_2940_ = l_Nat_reprFast(v_depth_2933_);
v___x_2941_ = lean_string_append(v___x_2939_, v___x_2940_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2943_ = lean_string_append(v___x_2941_, v___x_2942_);
v___x_2944_ = l_Nat_reprFast(v_tailSize_2934_);
v___x_2945_ = lean_string_append(v___x_2943_, v___x_2944_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2947_ = lean_string_append(v___x_2945_, v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2950_, lean_object* v_j_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_zero_2953_; uint8_t v_isZero_2954_; 
v_zero_2953_ = lean_unsigned_to_nat(0u);
v_isZero_2954_ = lean_nat_dec_eq(v_j_2951_, v_zero_2953_);
if (v_isZero_2954_ == 1)
{
lean_dec(v_j_2951_);
lean_dec(v_v_2950_);
return v_a_2952_;
}
else
{
lean_object* v_one_2955_; lean_object* v_n_2956_; lean_object* v___x_2957_; 
v_one_2955_ = lean_unsigned_to_nat(1u);
v_n_2956_ = lean_nat_sub(v_j_2951_, v_one_2955_);
lean_dec(v_j_2951_);
lean_inc(v_v_2950_);
v___x_2957_ = l_Lean_PersistentArray_push___redArg(v_a_2952_, v_v_2950_);
v_j_2951_ = v_n_2956_;
v_a_2952_ = v___x_2957_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_mkPersistentArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_PersistentArray_empty(lean_box(0));
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2960_, lean_object* v_v_2961_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_2963_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2961_, v_n_2960_, v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2964_, lean_object* v_n_2965_, lean_object* v_v_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_mkPersistentArray___redArg(v_n_2965_, v_v_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2968_, lean_object* v_v_2969_, lean_object* v_n_2970_, lean_object* v_j_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2969_, v_j_2971_, v_a_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_v_2976_, lean_object* v_n_2977_, lean_object* v_j_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2975_, v_v_2976_, v_n_2977_, v_j_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_n_2977_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2982_, lean_object* v_v_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_mkPersistentArray___redArg(v_n_2982_, v_v_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2985_, lean_object* v_n_2986_, lean_object* v_v_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_mkPersistentArray___redArg(v_n_2986_, v_v_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
if (lean_obj_tag(v_a_2989_) == 0)
{
return v_a_2990_;
}
else
{
lean_object* v_head_2991_; lean_object* v_tail_2992_; lean_object* v___x_2993_; 
v_head_2991_ = lean_ctor_get(v_a_2989_, 0);
lean_inc(v_head_2991_);
v_tail_2992_ = lean_ctor_get(v_a_2989_, 1);
lean_inc(v_tail_2992_);
lean_dec_ref(v_a_2989_);
v___x_2993_ = l_Lean_PersistentArray_push___redArg(v_a_2990_, v_head_2991_);
v_a_2989_ = v_tail_2992_;
v_a_2990_ = v___x_2993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop(lean_object* v_00_u03b1_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(v_a_2996_, v_a_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_List_toPArray_x27___redArg(lean_object* v_xs_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3000_ = lean_unsigned_to_nat(32u);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_3000_);
lean_dec_ref(v___x_3001_);
v___x_3002_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__1, &l_Lean_PersistentArray_empty___closed__1_once, _init_l_Lean_PersistentArray_empty___closed__1);
v___x_3003_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(v_xs_2999_, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_List_toPArray_x27(lean_object* v_00_u03b1_3004_, lean_object* v_xs_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_List_toPArray_x27___redArg(v_xs_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg(lean_object* v_xs_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3008_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_array_get_size(v_xs_3007_);
v___x_3011_ = lean_nat_dec_lt(v___x_3009_, v___x_3010_);
if (v___x_3011_ == 0)
{
return v___x_3008_;
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_nat_dec_le(v___x_3010_, v___x_3010_);
if (v___x_3012_ == 0)
{
if (v___x_3011_ == 0)
{
return v___x_3008_;
}
else
{
size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_usize_of_nat(v___x_3010_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_3007_, v___x_3013_, v___x_3014_, v___x_3008_);
return v___x_3015_;
}
}
else
{
size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3010_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_3007_, v___x_3016_, v___x_3017_, v___x_3008_);
return v___x_3018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Array_toPArray_x27___redArg(v_xs_3019_);
lean_dec_ref(v_xs_3019_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27(lean_object* v_00_u03b1_3021_, lean_object* v_xs_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Array_toPArray_x27___redArg(v_xs_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_3024_, lean_object* v_xs_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Array_toPArray_x27(v_00_u03b1_3024_, v_xs_3025_);
lean_dec_ref(v_xs_3025_);
return v_res_3026_;
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
