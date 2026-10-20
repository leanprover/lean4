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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg(){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(32u);
v___x_613_ = lean_mk_empty_array_with_capacity(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg___boxed(lean_object* v___dummy_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v_res_615_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
lean_object* v_cs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_673_; 
v_cs_623_ = lean_ctor_get(v_x_622_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_673_ == 0)
{
v___x_625_ = v_x_622_;
v_isShared_626_ = v_isSharedCheck_673_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_cs_623_);
lean_dec(v_x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_673_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_array_get_size(v_cs_623_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v_idx_631_; lean_object* v_last_632_; lean_object* v___x_633_; lean_object* v_fst_634_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v_idx_631_ = lean_nat_sub(v___x_627_, v___x_630_);
v_last_632_ = lean_array_fget_borrowed(v_cs_623_, v_idx_631_);
lean_inc(v_last_632_);
v___x_633_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_632_);
v_fst_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_fst_634_);
if (lean_obj_tag(v_fst_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_idx_631_);
lean_del_object(v___x_625_);
lean_dec_ref(v_cs_623_);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_643_ = lean_ctor_get(v___x_633_, 1);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_644_);
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_snd_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_670_; 
v_snd_645_ = lean_ctor_get(v___x_633_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_671_);
v___x_647_ = v___x_633_;
v_isShared_648_ = v_isSharedCheck_670_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_snd_645_);
lean_dec(v___x_633_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_670_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v_cs_x27_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_649_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v_cs_x27_650_ = lean_array_fset(v_cs_623_, v_idx_631_, v___x_649_);
v___x_651_ = lean_array_get_size(v_snd_645_);
v___x_652_ = lean_nat_dec_eq(v___x_651_, v___x_628_);
if (v___x_652_ == 0)
{
lean_object* v___x_654_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_snd_645_);
v___x_654_ = v___x_625_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_snd_645_);
v___x_654_ = v_reuseFailAlloc_659_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_655_ = lean_array_fset(v_cs_x27_650_, v_idx_631_, v___x_654_);
lean_dec(v_idx_631_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_655_);
v___x_657_ = v___x_647_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_cs_x27_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
lean_dec(v_snd_645_);
lean_dec(v_idx_631_);
lean_del_object(v___x_625_);
v_cs_x27_660_ = lean_array_pop(v_cs_x27_650_);
v___x_661_ = lean_array_get_size(v_cs_x27_660_);
v___x_662_ = lean_nat_dec_eq(v___x_661_, v___x_628_);
if (v___x_662_ == 0)
{
lean_object* v___x_664_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_cs_x27_660_);
v___x_664_ = v___x_647_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_cs_x27_660_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_668_; 
lean_dec_ref(v_cs_x27_660_);
v___x_666_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_666_);
v___x_668_ = v___x_647_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_634_);
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
}
}
}
else
{
lean_object* v___x_672_; 
lean_del_object(v___x_625_);
lean_dec_ref(v_cs_623_);
v___x_672_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
return v___x_672_;
}
}
}
else
{
lean_object* v_vs_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_vs_674_ = lean_ctor_get(v_x_622_, 0);
lean_inc_ref(v_vs_674_);
lean_dec_ref_known(v_x_622_, 1);
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_vs_674_);
v___x_676_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_681_){
_start:
{
lean_object* v_root_682_; lean_object* v_tail_683_; lean_object* v_size_684_; size_t v_shift_685_; lean_object* v_tailOff_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_root_682_ = lean_ctor_get(v_t_681_, 0);
v_tail_683_ = lean_ctor_get(v_t_681_, 1);
v_size_684_ = lean_ctor_get(v_t_681_, 2);
v_shift_685_ = lean_ctor_get_usize(v_t_681_, 4);
v_tailOff_686_ = lean_ctor_get(v_t_681_, 3);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_array_get_size(v_tail_683_);
v___x_689_ = lean_nat_dec_lt(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v_fst_691_; 
lean_inc_ref(v_root_682_);
v___x_690_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_682_);
v_fst_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_fst_691_);
if (lean_obj_tag(v_fst_691_) == 0)
{
lean_dec_ref(v___x_690_);
return v_t_681_;
}
else
{
lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_720_; 
lean_inc(v_size_684_);
v_isSharedCheck_720_ = !lean_is_exclusive(v_t_681_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_721_ = lean_ctor_get(v_t_681_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_t_681_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_t_681_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_t_681_, 0);
lean_dec(v_unused_724_);
v___x_693_ = v_t_681_;
v_isShared_694_ = v_isSharedCheck_720_;
goto v_resetjp_692_;
}
else
{
lean_dec(v_t_681_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_720_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_snd_695_; lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_719_; 
v_snd_695_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_snd_695_);
lean_dec_ref(v___x_690_);
v_val_696_ = lean_ctor_get(v_fst_691_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_fst_691_);
if (v_isSharedCheck_719_ == 0)
{
v___x_698_ = v_fst_691_;
v_isShared_699_ = v_isSharedCheck_719_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v_fst_691_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_719_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_last_700_; lean_object* v___x_701_; lean_object* v_newSize_702_; lean_object* v___x_703_; lean_object* v_newTailOff_704_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_last_700_ = lean_array_pop(v_val_696_);
v___x_701_ = lean_unsigned_to_nat(1u);
v_newSize_702_ = lean_nat_sub(v_size_684_, v___x_701_);
lean_dec(v_size_684_);
v___x_703_ = lean_array_get_size(v_last_700_);
v_newTailOff_704_ = lean_nat_sub(v_newSize_702_, v___x_703_);
v___x_712_ = lean_array_get_size(v_snd_695_);
v___x_713_ = lean_nat_dec_eq(v___x_712_, v___x_701_);
if (v___x_713_ == 0)
{
goto v___jp_705_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_array_fget_borrowed(v_snd_695_, v___x_687_);
v___x_715_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_714_);
if (v___x_715_ == 0)
{
goto v___jp_705_;
}
else
{
size_t v___x_716_; size_t v___x_717_; lean_object* v___x_718_; 
lean_inc(v___x_714_);
lean_del_object(v___x_698_);
lean_dec(v_snd_695_);
lean_del_object(v___x_693_);
v___x_716_ = ((size_t)5ULL);
v___x_717_ = lean_usize_sub(v_shift_685_, v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_718_, 0, v___x_714_);
lean_ctor_set(v___x_718_, 1, v_last_700_);
lean_ctor_set(v___x_718_, 2, v_newSize_702_);
lean_ctor_set(v___x_718_, 3, v_newTailOff_704_);
lean_ctor_set_usize(v___x_718_, 4, v___x_717_);
return v___x_718_;
}
}
v___jp_705_:
{
lean_object* v___x_707_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 0);
lean_ctor_set(v___x_698_, 0, v_snd_695_);
v___x_707_ = v___x_698_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_snd_695_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 3, v_newTailOff_704_);
lean_ctor_set(v___x_693_, 2, v_newSize_702_);
lean_ctor_set(v___x_693_, 1, v_last_700_);
lean_ctor_set(v___x_693_, 0, v___x_707_);
v___x_709_ = v___x_693_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_last_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_newSize_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_newTailOff_704_);
lean_ctor_set_usize(v_reuseFailAlloc_710_, 4, v_shift_685_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_734_; 
lean_inc(v_tailOff_686_);
lean_inc(v_size_684_);
lean_inc_ref(v_tail_683_);
lean_inc_ref(v_root_682_);
v_isSharedCheck_734_ = !lean_is_exclusive(v_t_681_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_735_ = lean_ctor_get(v_t_681_, 3);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_t_681_, 2);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_t_681_, 1);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_t_681_, 0);
lean_dec(v_unused_738_);
v___x_726_ = v_t_681_;
v_isShared_727_ = v_isSharedCheck_734_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_t_681_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_734_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_728_ = lean_array_pop(v_tail_683_);
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_sub(v_size_684_, v___x_729_);
lean_dec(v_size_684_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 2, v___x_730_);
lean_ctor_set(v___x_726_, 1, v___x_728_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_root_682_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_tailOff_686_);
lean_ctor_set_usize(v_reuseFailAlloc_733_, 4, v_shift_685_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_739_, lean_object* v_t_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentArray_pop___redArg(v_t_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_742_, lean_object* v_f_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_toApplicative_746_; lean_object* v_cs_747_; lean_object* v_toPure_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_toApplicative_746_ = lean_ctor_get(v_inst_742_, 0);
v_cs_747_ = lean_ctor_get(v_x_744_, 0);
lean_inc_ref(v_cs_747_);
lean_dec_ref_known(v_x_744_, 1);
v_toPure_748_ = lean_ctor_get(v_toApplicative_746_, 1);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_cs_747_);
v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_inc(v_toPure_748_);
lean_dec_ref(v_cs_747_);
lean_dec(v_f_743_);
lean_dec_ref(v_inst_742_);
v___x_752_ = lean_apply_2(v_toPure_748_, lean_box(0), v_x_745_);
return v___x_752_;
}
else
{
lean_object* v___f_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
lean_inc_ref(v_inst_742_);
v___f_753_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_753_, 0, v_inst_742_);
lean_closure_set(v___f_753_, 1, v_f_743_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_750_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_742_, v___f_753_, v_cs_747_, v___x_754_, v___x_755_, v_x_745_);
return v___x_756_;
}
}
else
{
lean_object* v_toApplicative_757_; lean_object* v_vs_758_; lean_object* v_toPure_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_toApplicative_757_ = lean_ctor_get(v_inst_742_, 0);
v_vs_758_ = lean_ctor_get(v_x_744_, 0);
lean_inc_ref(v_vs_758_);
lean_dec_ref_known(v_x_744_, 1);
v_toPure_759_ = lean_ctor_get(v_toApplicative_757_, 1);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v_vs_758_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_inc(v_toPure_759_);
lean_dec_ref(v_vs_758_);
lean_dec(v_f_743_);
lean_dec_ref(v_inst_742_);
v___x_763_ = lean_apply_2(v_toPure_759_, lean_box(0), v_x_745_);
return v___x_763_;
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_761_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_742_, v_f_743_, v_vs_758_, v___x_764_, v___x_765_, v_x_745_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_767_, lean_object* v_f_768_, lean_object* v_b_769_, lean_object* v_c_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_767_, v_f_768_, v_c_770_, v_b_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_772_, lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_00_u03b2_775_, lean_object* v_f_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_774_, v_f_776_, v_x_777_, v_x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_toApplicative_780_, lean_object* v_j_781_, lean_object* v_cs_782_, lean_object* v_inst_783_, lean_object* v___f_784_, lean_object* v_b_785_){
_start:
{
lean_object* v_toPure_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_toPure_786_ = lean_ctor_get(v_toApplicative_780_, 1);
lean_inc(v_toPure_786_);
lean_dec_ref(v_toApplicative_780_);
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_j_781_, v___x_787_);
v___x_789_ = lean_array_get_size(v_cs_782_);
v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v___x_788_);
lean_dec(v___f_784_);
lean_dec_ref(v_inst_783_);
lean_dec_ref(v_cs_782_);
v___x_791_ = lean_apply_2(v_toPure_786_, lean_box(0), v_b_785_);
return v___x_791_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
lean_dec(v_toPure_786_);
v___x_792_ = lean_usize_of_nat(v___x_788_);
lean_dec(v___x_788_);
v___x_793_ = lean_usize_of_nat(v___x_789_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_783_, v___f_784_, v_cs_782_, v___x_792_, v___x_793_, v_b_785_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_795_, lean_object* v_j_796_, lean_object* v_cs_797_, lean_object* v_inst_798_, lean_object* v___f_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_toApplicative_795_, v_j_796_, v_cs_797_, v_inst_798_, v___f_799_, v_b_800_);
lean_dec(v_j_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_x_804_, size_t v_x_805_, size_t v_x_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
lean_object* v_toApplicative_808_; lean_object* v_toBind_809_; lean_object* v_cs_810_; lean_object* v___f_811_; lean_object* v___x_812_; size_t v___x_813_; lean_object* v_j_814_; lean_object* v___f_815_; lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_toApplicative_808_ = lean_ctor_get(v_inst_802_, 0);
v_toBind_809_ = lean_ctor_get(v_inst_802_, 1);
lean_inc(v_toBind_809_);
v_cs_810_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref_n(v_cs_810_, 2);
lean_dec_ref_known(v_x_804_, 1);
lean_inc(v_f_803_);
lean_inc_ref_n(v_inst_802_, 2);
v___f_811_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_811_, 0, v_inst_802_);
lean_closure_set(v___f_811_, 1, v_f_803_);
v___x_812_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_813_ = lean_usize_shift_right(v_x_805_, v_x_806_);
v_j_814_ = lean_usize_to_nat(v___x_813_);
lean_inc(v_j_814_);
lean_inc_ref(v_toApplicative_808_);
v___f_815_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_815_, 0, v_toApplicative_808_);
lean_closure_set(v___f_815_, 1, v_j_814_);
lean_closure_set(v___f_815_, 2, v_cs_810_);
lean_closure_set(v___f_815_, 3, v_inst_802_);
lean_closure_set(v___f_815_, 4, v___f_811_);
v___x_816_ = lean_array_get(v___x_812_, v_cs_810_, v_j_814_);
lean_dec(v_j_814_);
lean_dec_ref(v_cs_810_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_shift_left(v___x_817_, v_x_806_);
v___x_819_ = lean_usize_sub(v___x_818_, v___x_817_);
v___x_820_ = lean_usize_land(v_x_805_, v___x_819_);
v___x_821_ = ((size_t)5ULL);
v___x_822_ = lean_usize_sub(v_x_806_, v___x_821_);
v___x_823_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_802_, v_f_803_, v___x_816_, v___x_820_, v___x_822_, v_x_807_);
v___x_824_ = lean_apply_4(v_toBind_809_, lean_box(0), lean_box(0), v___x_823_, v___f_815_);
return v___x_824_;
}
else
{
lean_object* v_toApplicative_825_; lean_object* v_vs_826_; lean_object* v_toPure_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_toApplicative_825_ = lean_ctor_get(v_inst_802_, 0);
v_vs_826_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref(v_vs_826_);
lean_dec_ref_known(v_x_804_, 1);
v_toPure_827_ = lean_ctor_get(v_toApplicative_825_, 1);
v___x_828_ = lean_usize_to_nat(v_x_805_);
v___x_829_ = lean_array_get_size(v_vs_826_);
v___x_830_ = lean_nat_dec_lt(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_inc(v_toPure_827_);
lean_dec(v___x_828_);
lean_dec_ref(v_vs_826_);
lean_dec(v_f_803_);
lean_dec_ref(v_inst_802_);
v___x_831_ = lean_apply_2(v_toPure_827_, lean_box(0), v_x_807_);
return v___x_831_;
}
else
{
size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_usize_of_nat(v___x_828_);
lean_dec(v___x_828_);
v___x_833_ = lean_usize_of_nat(v___x_829_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_802_, v_f_803_, v_vs_826_, v___x_832_, v___x_833_, v_x_807_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_835_, lean_object* v_f_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
size_t v_x_192__boxed_841_; size_t v_x_193__boxed_842_; lean_object* v_res_843_; 
v_x_192__boxed_841_ = lean_unbox_usize(v_x_838_);
lean_dec(v_x_838_);
v_x_193__boxed_842_ = lean_unbox_usize(v_x_839_);
lean_dec(v_x_839_);
v_res_843_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_835_, v_f_836_, v_x_837_, v_x_192__boxed_841_, v_x_193__boxed_842_, v_x_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_844_, lean_object* v_m_845_, lean_object* v_inst_846_, lean_object* v_00_u03b2_847_, lean_object* v_f_848_, lean_object* v_x_849_, size_t v_x_850_, size_t v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_846_, v_f_848_, v_x_849_, v_x_850_, v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_854_, lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_00_u03b2_857_, lean_object* v_f_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_251__boxed_863_; size_t v_x_252__boxed_864_; lean_object* v_res_865_; 
v_x_251__boxed_863_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_x_252__boxed_864_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_res_865_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_854_, v_m_855_, v_inst_856_, v_00_u03b2_857_, v_f_858_, v_x_859_, v_x_251__boxed_863_, v_x_252__boxed_864_, v_x_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_toApplicative_866_, lean_object* v_tail_867_, lean_object* v___x_868_, lean_object* v_inst_869_, lean_object* v_f_870_, lean_object* v_b_871_){
_start:
{
lean_object* v_toPure_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_toPure_872_ = lean_ctor_get(v_toApplicative_866_, 1);
lean_inc(v_toPure_872_);
lean_dec_ref(v_toApplicative_866_);
v___x_873_ = lean_array_get_size(v_tail_867_);
v___x_874_ = lean_nat_dec_lt(v___x_868_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec(v_f_870_);
lean_dec_ref(v_inst_869_);
lean_dec_ref(v_tail_867_);
v___x_875_ = lean_apply_2(v_toPure_872_, lean_box(0), v_b_871_);
return v___x_875_;
}
else
{
size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; 
lean_dec(v_toPure_872_);
v___x_876_ = ((size_t)0ULL);
v___x_877_ = lean_usize_of_nat(v___x_873_);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_869_, v_f_870_, v_tail_867_, v___x_876_, v___x_877_, v_b_871_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_toApplicative_879_, lean_object* v_tail_880_, lean_object* v___x_881_, lean_object* v_inst_882_, lean_object* v_f_883_, lean_object* v_b_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_toApplicative_879_, v_tail_880_, v___x_881_, v_inst_882_, v_f_883_, v_b_884_);
lean_dec(v___x_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_886_, lean_object* v_t_887_, lean_object* v_f_888_, lean_object* v_init_889_, lean_object* v_start_890_){
_start:
{
lean_object* v_toApplicative_891_; lean_object* v_toBind_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_toApplicative_891_ = lean_ctor_get(v_inst_886_, 0);
v_toBind_892_ = lean_ctor_get(v_inst_886_, 1);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_nat_dec_eq(v_start_890_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v_root_895_; lean_object* v_tail_896_; size_t v_shift_897_; lean_object* v_tailOff_898_; uint8_t v___x_899_; 
v_root_895_ = lean_ctor_get(v_t_887_, 0);
lean_inc_ref(v_root_895_);
v_tail_896_ = lean_ctor_get(v_t_887_, 1);
lean_inc_ref(v_tail_896_);
v_shift_897_ = lean_ctor_get_usize(v_t_887_, 4);
v_tailOff_898_ = lean_ctor_get(v_t_887_, 3);
lean_inc(v_tailOff_898_);
lean_dec_ref(v_t_887_);
v___x_899_ = lean_nat_dec_le(v_tailOff_898_, v_start_890_);
if (v___x_899_ == 0)
{
lean_object* v___f_900_; size_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
lean_inc(v_toBind_892_);
lean_dec(v_tailOff_898_);
lean_inc(v_f_888_);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v_toApplicative_891_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_900_, 0, v_toApplicative_891_);
lean_closure_set(v___f_900_, 1, v_tail_896_);
lean_closure_set(v___f_900_, 2, v___x_893_);
lean_closure_set(v___f_900_, 3, v_inst_886_);
lean_closure_set(v___f_900_, 4, v_f_888_);
v___x_901_ = lean_usize_of_nat(v_start_890_);
v___x_902_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_886_, v_f_888_, v_root_895_, v___x_901_, v_shift_897_, v_init_889_);
v___x_903_ = lean_apply_4(v_toBind_892_, lean_box(0), lean_box(0), v___x_902_, v___f_900_);
return v___x_903_;
}
else
{
lean_object* v_toPure_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
lean_dec_ref(v_root_895_);
v_toPure_904_ = lean_ctor_get(v_toApplicative_891_, 1);
v___x_905_ = lean_nat_sub(v_start_890_, v_tailOff_898_);
lean_dec(v_tailOff_898_);
v___x_906_ = lean_array_get_size(v_tail_896_);
v___x_907_ = lean_nat_dec_lt(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_inc(v_toPure_904_);
lean_dec(v___x_905_);
lean_dec_ref(v_tail_896_);
lean_dec(v_f_888_);
lean_dec_ref(v_inst_886_);
v___x_908_ = lean_apply_2(v_toPure_904_, lean_box(0), v_init_889_);
return v___x_908_;
}
else
{
size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_usize_of_nat(v___x_905_);
lean_dec(v___x_905_);
v___x_910_ = lean_usize_of_nat(v___x_906_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_886_, v_f_888_, v_tail_896_, v___x_909_, v___x_910_, v_init_889_);
return v___x_911_;
}
}
}
else
{
lean_object* v_root_912_; lean_object* v_tail_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_inc(v_toBind_892_);
v_root_912_ = lean_ctor_get(v_t_887_, 0);
lean_inc_ref(v_root_912_);
v_tail_913_ = lean_ctor_get(v_t_887_, 1);
lean_inc_ref(v_tail_913_);
lean_dec_ref(v_t_887_);
lean_inc(v_f_888_);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v_toApplicative_891_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_914_, 0, v_toApplicative_891_);
lean_closure_set(v___f_914_, 1, v_tail_913_);
lean_closure_set(v___f_914_, 2, v___x_893_);
lean_closure_set(v___f_914_, 3, v_inst_886_);
lean_closure_set(v___f_914_, 4, v_f_888_);
v___x_915_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_886_, v_f_888_, v_root_912_, v_init_889_);
v___x_916_ = lean_apply_4(v_toBind_892_, lean_box(0), lean_box(0), v___x_915_, v___f_914_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_917_, lean_object* v_t_918_, lean_object* v_f_919_, lean_object* v_init_920_, lean_object* v_start_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_917_, v_t_918_, v_f_919_, v_init_920_, v_start_921_);
lean_dec(v_start_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_923_, lean_object* v_m_924_, lean_object* v_inst_925_, lean_object* v_00_u03b2_926_, lean_object* v_t_927_, lean_object* v_f_928_, lean_object* v_init_929_, lean_object* v_start_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_925_, v_t_927_, v_f_928_, v_init_929_, v_start_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_932_, lean_object* v_m_933_, lean_object* v_inst_934_, lean_object* v_00_u03b2_935_, lean_object* v_t_936_, lean_object* v_f_937_, lean_object* v_init_938_, lean_object* v_start_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_932_, v_m_933_, v_inst_934_, v_00_u03b2_935_, v_t_936_, v_f_937_, v_init_938_, v_start_939_);
lean_dec(v_start_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_941_, lean_object* v_f_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v_toApplicative_945_; lean_object* v_cs_946_; lean_object* v_toPure_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_toApplicative_945_ = lean_ctor_get(v_inst_941_, 0);
v_cs_946_ = lean_ctor_get(v_x_943_, 0);
lean_inc_ref(v_cs_946_);
lean_dec_ref_known(v_x_943_, 1);
v_toPure_947_ = lean_ctor_get(v_toApplicative_945_, 1);
v___x_948_ = lean_array_get_size(v_cs_946_);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_nat_dec_lt(v___x_949_, v___x_948_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_inc(v_toPure_947_);
lean_dec_ref(v_cs_946_);
lean_dec(v_f_942_);
lean_dec_ref(v_inst_941_);
v___x_951_ = lean_apply_2(v_toPure_947_, lean_box(0), v_x_944_);
return v___x_951_;
}
else
{
lean_object* v___f_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_inc_ref(v_inst_941_);
v___f_952_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_952_, 0, v_inst_941_);
lean_closure_set(v___f_952_, 1, v_f_942_);
v___x_953_ = lean_usize_of_nat(v___x_948_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_941_, v___f_952_, v_cs_946_, v___x_953_, v___x_954_, v_x_944_);
return v___x_955_;
}
}
else
{
lean_object* v_toApplicative_956_; lean_object* v_vs_957_; lean_object* v_toPure_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_toApplicative_956_ = lean_ctor_get(v_inst_941_, 0);
v_vs_957_ = lean_ctor_get(v_x_943_, 0);
lean_inc_ref(v_vs_957_);
lean_dec_ref_known(v_x_943_, 1);
v_toPure_958_ = lean_ctor_get(v_toApplicative_956_, 1);
v___x_959_ = lean_array_get_size(v_vs_957_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_nat_dec_lt(v___x_960_, v___x_959_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_inc(v_toPure_958_);
lean_dec_ref(v_vs_957_);
lean_dec(v_f_942_);
lean_dec_ref(v_inst_941_);
v___x_962_ = lean_apply_2(v_toPure_958_, lean_box(0), v_x_944_);
return v___x_962_;
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_usize_of_nat(v___x_959_);
v___x_964_ = ((size_t)0ULL);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_941_, v_f_942_, v_vs_957_, v___x_963_, v___x_964_, v_x_944_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_966_, lean_object* v_f_967_, lean_object* v_c_968_, lean_object* v_b_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_966_, v_f_967_, v_c_968_, v_b_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_971_, lean_object* v_m_972_, lean_object* v_00_u03b2_973_, lean_object* v_inst_974_, lean_object* v_f_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_974_, v_f_975_, v_x_976_, v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_979_, lean_object* v_f_980_, lean_object* v_root_981_, lean_object* v_____do__lift_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_979_, v_f_980_, v_root_981_, v_____do__lift_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_984_, lean_object* v_t_985_, lean_object* v_f_986_, lean_object* v_init_987_){
_start:
{
lean_object* v_toApplicative_988_; lean_object* v_toBind_989_; lean_object* v_root_990_; lean_object* v_tail_991_; lean_object* v_toPure_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_toApplicative_988_ = lean_ctor_get(v_inst_984_, 0);
v_toBind_989_ = lean_ctor_get(v_inst_984_, 1);
lean_inc(v_toBind_989_);
v_root_990_ = lean_ctor_get(v_t_985_, 0);
lean_inc_ref(v_root_990_);
v_tail_991_ = lean_ctor_get(v_t_985_, 1);
lean_inc_ref(v_tail_991_);
lean_dec_ref(v_t_985_);
v_toPure_992_ = lean_ctor_get(v_toApplicative_988_, 1);
lean_inc(v_f_986_);
lean_inc_ref(v_inst_984_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_993_, 0, v_inst_984_);
lean_closure_set(v___f_993_, 1, v_f_986_);
lean_closure_set(v___f_993_, 2, v_root_990_);
v___x_994_ = lean_array_get_size(v_tail_991_);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_nat_dec_lt(v___x_995_, v___x_994_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc(v_toPure_992_);
lean_dec_ref(v_tail_991_);
lean_dec(v_f_986_);
lean_dec_ref(v_inst_984_);
v___x_997_ = lean_apply_2(v_toPure_992_, lean_box(0), v_init_987_);
v___x_998_ = lean_apply_4(v_toBind_989_, lean_box(0), lean_box(0), v___x_997_, v___f_993_);
return v___x_998_;
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_999_ = lean_usize_of_nat(v___x_994_);
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_984_, v_f_986_, v_tail_991_, v___x_999_, v___x_1000_, v_init_987_);
v___x_1002_ = lean_apply_4(v_toBind_989_, lean_box(0), lean_box(0), v___x_1001_, v___f_993_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1003_, lean_object* v_m_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_inst_1006_, lean_object* v_t_1007_, lean_object* v_f_1008_, lean_object* v_init_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1006_, v_t_1007_, v_f_1008_, v_init_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1011_, lean_object* v_____s_1012_){
_start:
{
lean_object* v_fst_1013_; 
v_fst_1013_ = lean_ctor_get(v_____s_1012_, 0);
if (lean_obj_tag(v_fst_1013_) == 0)
{
lean_object* v_snd_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_snd_1014_ = lean_ctor_get(v_____s_1012_, 1);
lean_inc(v_snd_1014_);
lean_dec_ref(v_____s_1012_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_snd_1014_);
v___x_1016_ = lean_apply_2(v_toPure_1011_, lean_box(0), v___x_1015_);
return v___x_1016_;
}
else
{
lean_object* v_val_1017_; lean_object* v___x_1018_; 
lean_inc_ref(v_fst_1013_);
lean_dec_ref(v_____s_1012_);
v_val_1017_ = lean_ctor_get(v_fst_1013_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v_fst_1013_, 1);
v___x_1018_ = lean_apply_2(v_toPure_1011_, lean_box(0), v_val_1017_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1019_, lean_object* v_toPure_1020_, lean_object* v___x_1021_, lean_object* v_____do__lift_1022_){
_start:
{
if (lean_obj_tag(v_____do__lift_1022_) == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec(v___x_1021_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_____do__lift_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_snd_1019_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
v___x_1026_ = lean_apply_2(v_toPure_1020_, lean_box(0), v___x_1025_);
return v___x_1026_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_snd_1019_);
v_a_1027_ = lean_ctor_get(v_____do__lift_1022_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_____do__lift_1022_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1029_ = v_____do__lift_1022_;
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v_____do__lift_1022_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1021_);
lean_ctor_set(v___x_1031_, 1, v_a_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_apply_2(v_toPure_1020_, lean_box(0), v___x_1033_);
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1037_, lean_object* v___x_1038_, lean_object* v_f_1039_, lean_object* v_toBind_1040_, lean_object* v_a_1041_, lean_object* v_x_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_snd_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_snd_1044_ = lean_ctor_get(v___y_1043_, 1);
lean_inc_n(v_snd_1044_, 2);
lean_dec_ref(v___y_1043_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1045_, 0, v_snd_1044_);
lean_closure_set(v___f_1045_, 1, v_toPure_1037_);
lean_closure_set(v___f_1045_, 2, v___x_1038_);
v___x_1046_ = lean_apply_2(v_f_1039_, v_a_1041_, v_snd_1044_);
v___x_1047_ = lean_apply_4(v_toBind_1040_, lean_box(0), lean_box(0), v___x_1046_, v___f_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1048_, lean_object* v___x_1049_, lean_object* v_inst_1050_, lean_object* v_f_1051_, lean_object* v_toBind_1052_, lean_object* v_a_1053_, lean_object* v_x_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1048_, v___x_1049_, v_inst_1050_, v_f_1051_, v_toBind_1052_, v_a_1053_, v_x_1054_, v___y_1055_);
lean_dec_ref(v_a_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1057_, lean_object* v_f_1058_, lean_object* v_n_1059_, lean_object* v_b_1060_){
_start:
{
if (lean_obj_tag(v_n_1059_) == 0)
{
lean_object* v_toApplicative_1061_; lean_object* v_toBind_1062_; lean_object* v_toPure_1063_; lean_object* v_cs_1064_; lean_object* v___f_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_toApplicative_1061_ = lean_ctor_get(v_inst_1057_, 0);
v_toBind_1062_ = lean_ctor_get(v_inst_1057_, 1);
lean_inc_n(v_toBind_1062_, 2);
v_toPure_1063_ = lean_ctor_get(v_toApplicative_1061_, 1);
v_cs_1064_ = lean_ctor_get(v_n_1059_, 0);
lean_inc_n(v_toPure_1063_, 2);
v___f_1065_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1065_, 0, v_toPure_1063_);
v___x_1066_ = lean_box(0);
lean_inc_ref(v_inst_1057_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1067_, 0, v_toPure_1063_);
lean_closure_set(v___f_1067_, 1, v___x_1066_);
lean_closure_set(v___f_1067_, 2, v_inst_1057_);
lean_closure_set(v___f_1067_, 3, v_f_1058_);
lean_closure_set(v___f_1067_, 4, v_toBind_1062_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v_b_1060_);
v_sz_1069_ = lean_array_size(v_cs_1064_);
v___x_1070_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1064_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1057_, v_cs_1064_, v___f_1067_, v_sz_1069_, v___x_1070_, v___x_1068_);
v___x_1072_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v___x_1071_, v___f_1065_);
return v___x_1072_;
}
else
{
lean_object* v_toApplicative_1073_; lean_object* v_toBind_1074_; lean_object* v_toPure_1075_; lean_object* v_vs_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_toApplicative_1073_ = lean_ctor_get(v_inst_1057_, 0);
v_toBind_1074_ = lean_ctor_get(v_inst_1057_, 1);
lean_inc_n(v_toBind_1074_, 2);
v_toPure_1075_ = lean_ctor_get(v_toApplicative_1073_, 1);
v_vs_1076_ = lean_ctor_get(v_n_1059_, 0);
lean_inc_n(v_toPure_1075_, 2);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1077_, 0, v_toPure_1075_);
v___x_1078_ = lean_box(0);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1079_, 0, v_toPure_1075_);
lean_closure_set(v___f_1079_, 1, v___x_1078_);
lean_closure_set(v___f_1079_, 2, v_f_1058_);
lean_closure_set(v___f_1079_, 3, v_toBind_1074_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v_b_1060_);
v_sz_1081_ = lean_array_size(v_vs_1076_);
v___x_1082_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1076_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1057_, v_vs_1076_, v___f_1079_, v_sz_1081_, v___x_1082_, v___x_1080_);
v___x_1084_ = lean_apply_4(v_toBind_1074_, lean_box(0), lean_box(0), v___x_1083_, v___f_1077_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1085_, lean_object* v___x_1086_, lean_object* v_inst_1087_, lean_object* v_f_1088_, lean_object* v_toBind_1089_, lean_object* v_a_1090_, lean_object* v_x_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_snd_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_snd_1093_ = lean_ctor_get(v___y_1092_, 1);
lean_inc_n(v_snd_1093_, 2);
lean_dec_ref(v___y_1092_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1094_, 0, v_snd_1093_);
lean_closure_set(v___f_1094_, 1, v_toPure_1085_);
lean_closure_set(v___f_1094_, 2, v___x_1086_);
v___x_1095_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1087_, v_f_1088_, v_a_1090_, v_snd_1093_);
v___x_1096_ = lean_apply_4(v_toBind_1089_, lean_box(0), lean_box(0), v___x_1095_, v___f_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1097_, lean_object* v_f_1098_, lean_object* v_n_1099_, lean_object* v_b_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1097_, v_f_1098_, v_n_1099_, v_b_1100_);
lean_dec_ref(v_n_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_m_1104_, lean_object* v_inst_1105_, lean_object* v_inh_1106_, lean_object* v_f_1107_, lean_object* v_n_1108_, lean_object* v_b_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1105_, v_f_1107_, v_n_1108_, v_b_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_m_1113_, lean_object* v_inst_1114_, lean_object* v_inh_1115_, lean_object* v_f_1116_, lean_object* v_n_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1111_, v_00_u03b2_1112_, v_m_1113_, v_inst_1114_, v_inh_1115_, v_f_1116_, v_n_1117_, v_b_1118_);
lean_dec_ref(v_n_1117_);
lean_dec(v_inh_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1120_, lean_object* v_____s_1121_){
_start:
{
lean_object* v_fst_1122_; 
v_fst_1122_ = lean_ctor_get(v_____s_1121_, 0);
if (lean_obj_tag(v_fst_1122_) == 0)
{
lean_object* v_snd_1123_; lean_object* v___x_1124_; 
v_snd_1123_ = lean_ctor_get(v_____s_1121_, 1);
lean_inc(v_snd_1123_);
lean_dec_ref(v_____s_1121_);
v___x_1124_ = lean_apply_2(v_toPure_1120_, lean_box(0), v_snd_1123_);
return v___x_1124_;
}
else
{
lean_object* v_val_1125_; lean_object* v___x_1126_; 
lean_inc_ref(v_fst_1122_);
lean_dec_ref(v_____s_1121_);
v_val_1125_ = lean_ctor_get(v_fst_1122_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v_fst_1122_, 1);
v___x_1126_ = lean_apply_2(v_toPure_1120_, lean_box(0), v_val_1125_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1127_, lean_object* v_toPure_1128_, lean_object* v___x_1129_, lean_object* v_____do__lift_1130_){
_start:
{
if (lean_obj_tag(v_____do__lift_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v___x_1129_);
v_a_1131_ = lean_ctor_get(v_____do__lift_1130_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_____do__lift_1130_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1133_ = v_____do__lift_1130_;
v_isShared_1134_ = v_isSharedCheck_1141_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v_____do__lift_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1141_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_a_1131_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_snd_1127_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1136_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_apply_2(v_toPure_1128_, lean_box(0), v___x_1138_);
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_snd_1127_);
v_a_1142_ = lean_ctor_get(v_____do__lift_1130_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_____do__lift_1130_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1144_ = v_____do__lift_1130_;
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v_____do__lift_1130_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1129_);
lean_ctor_set(v___x_1146_, 1, v_a_1142_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_apply_2(v_toPure_1128_, lean_box(0), v___x_1148_);
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1152_, lean_object* v___x_1153_, lean_object* v_f_1154_, lean_object* v_toBind_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_snd_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_snd_1159_ = lean_ctor_get(v___y_1158_, 1);
lean_inc_n(v_snd_1159_, 2);
lean_dec_ref(v___y_1158_);
v___f_1160_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1160_, 0, v_snd_1159_);
lean_closure_set(v___f_1160_, 1, v_toPure_1152_);
lean_closure_set(v___f_1160_, 2, v___x_1153_);
v___x_1161_ = lean_apply_2(v_f_1154_, v_a_1156_, v_snd_1159_);
v___x_1162_ = lean_apply_4(v_toBind_1155_, lean_box(0), lean_box(0), v___x_1161_, v___f_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1163_, lean_object* v_f_1164_, lean_object* v_toBind_1165_, lean_object* v_tail_1166_, lean_object* v_inst_1167_, lean_object* v___f_1168_, lean_object* v_____do__lift_1169_){
_start:
{
if (lean_obj_tag(v_____do__lift_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; 
lean_dec(v___f_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_tail_1166_);
lean_dec(v_toBind_1165_);
lean_dec(v_f_1164_);
v_a_1170_ = lean_ctor_get(v_____do__lift_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v_____do__lift_1169_, 1);
v___x_1171_ = lean_apply_2(v_toPure_1163_, lean_box(0), v_a_1170_);
return v___x_1171_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; size_t v_sz_1176_; size_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1172_ = lean_ctor_get(v_____do__lift_1169_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v_____do__lift_1169_, 1);
v___x_1173_ = lean_box(0);
lean_inc(v_toBind_1165_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1174_, 0, v_toPure_1163_);
lean_closure_set(v___f_1174_, 1, v___x_1173_);
lean_closure_set(v___f_1174_, 2, v_f_1164_);
lean_closure_set(v___f_1174_, 3, v_toBind_1165_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v_a_1172_);
v_sz_1176_ = lean_array_size(v_tail_1166_);
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1167_, v_tail_1166_, v___f_1174_, v_sz_1176_, v___x_1177_, v___x_1175_);
v___x_1179_ = lean_apply_4(v_toBind_1165_, lean_box(0), lean_box(0), v___x_1178_, v___f_1168_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1180_, lean_object* v_t_1181_, lean_object* v_init_1182_, lean_object* v_f_1183_){
_start:
{
lean_object* v_toApplicative_1184_; lean_object* v_toBind_1185_; lean_object* v_root_1186_; lean_object* v_tail_1187_; lean_object* v_toPure_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; 
v_toApplicative_1184_ = lean_ctor_get(v_inst_1180_, 0);
v_toBind_1185_ = lean_ctor_get(v_inst_1180_, 1);
lean_inc_n(v_toBind_1185_, 2);
v_root_1186_ = lean_ctor_get(v_t_1181_, 0);
v_tail_1187_ = lean_ctor_get(v_t_1181_, 1);
v_toPure_1188_ = lean_ctor_get(v_toApplicative_1184_, 1);
lean_inc_n(v_toPure_1188_, 2);
lean_inc(v_f_1183_);
lean_inc_ref(v_inst_1180_);
v___x_1189_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1180_, v_f_1183_, v_root_1186_, v_init_1182_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1190_, 0, v_toPure_1188_);
lean_inc_ref(v_tail_1187_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1191_, 0, v_toPure_1188_);
lean_closure_set(v___f_1191_, 1, v_f_1183_);
lean_closure_set(v___f_1191_, 2, v_toBind_1185_);
lean_closure_set(v___f_1191_, 3, v_tail_1187_);
lean_closure_set(v___f_1191_, 4, v_inst_1180_);
lean_closure_set(v___f_1191_, 5, v___f_1190_);
v___x_1192_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v___x_1189_, v___f_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1193_, lean_object* v_t_1194_, lean_object* v_init_1195_, lean_object* v_f_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1193_, v_t_1194_, v_init_1195_, v_f_1196_);
lean_dec_ref(v_t_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1198_, lean_object* v_m_1199_, lean_object* v_inst_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_t_1202_, lean_object* v_init_1203_, lean_object* v_f_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1200_, v_t_1202_, v_init_1203_, v_f_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1206_, lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_t_1210_, lean_object* v_init_1211_, lean_object* v_f_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1206_, v_m_1207_, v_inst_1208_, v_00_u03b2_1209_, v_t_1210_, v_init_1211_, v_f_1212_);
lean_dec_ref(v_t_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1215_, 0, lean_box(0));
lean_closure_set(v___x_1215_, 1, lean_box(0));
lean_closure_set(v___x_1215_, 2, v_inst_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1216_, lean_object* v_m_1217_, lean_object* v_inst_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1219_, 0, lean_box(0));
lean_closure_set(v___x_1219_, 1, lean_box(0));
lean_closure_set(v___x_1219_, 2, v_inst_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1220_, lean_object* v_____s_1221_){
_start:
{
lean_object* v_fst_1222_; 
v_fst_1222_ = lean_ctor_get(v_____s_1221_, 0);
lean_inc(v_fst_1222_);
lean_dec_ref(v_____s_1221_);
if (lean_obj_tag(v_fst_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_apply_2(v_toPure_1220_, lean_box(0), v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; lean_object* v___x_1226_; 
v_val_1225_ = lean_ctor_get(v_fst_1222_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v_fst_1222_, 1);
v___x_1226_ = lean_apply_2(v_toPure_1220_, lean_box(0), v_val_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1227_, lean_object* v_toPure_1228_, lean_object* v___x_1229_, lean_object* v_____do__lift_1230_){
_start:
{
if (lean_obj_tag(v_____do__lift_1230_) == 1)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v___x_1229_);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_____do__lift_1230_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1227_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
v___x_1234_ = lean_apply_2(v_toPure_1228_, lean_box(0), v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_____do__lift_1230_);
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1229_);
v___x_1236_ = lean_apply_2(v_toPure_1228_, lean_box(0), v___x_1235_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1237_, lean_object* v_toBind_1238_, lean_object* v___f_1239_, lean_object* v_a_1240_, lean_object* v_x_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_apply_1(v_f_1237_, v_a_1240_);
v___x_1244_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1243_, v___f_1239_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1245_, lean_object* v_toBind_1246_, lean_object* v___f_1247_, lean_object* v_a_1248_, lean_object* v_x_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1245_, v_toBind_1246_, v___f_1247_, v_a_1248_, v_x_1249_, v___y_1250_);
lean_dec_ref(v___y_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1255_, lean_object* v_f_1256_, lean_object* v_toBind_1257_, lean_object* v___f_1258_, lean_object* v_a_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1255_, v_f_1256_, v_toBind_1257_, v___f_1258_, v_a_1259_, v_x_1260_, v___y_1261_);
lean_dec_ref(v___y_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1263_, lean_object* v_f_1264_, lean_object* v_x_1265_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
lean_object* v_toApplicative_1266_; lean_object* v_cs_1267_; lean_object* v_toBind_1268_; lean_object* v_toPure_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; size_t v_sz_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_toApplicative_1266_ = lean_ctor_get(v_inst_1263_, 0);
v_cs_1267_ = lean_ctor_get(v_x_1265_, 0);
lean_inc_ref(v_cs_1267_);
lean_dec_ref_known(v_x_1265_, 1);
v_toBind_1268_ = lean_ctor_get(v_inst_1263_, 1);
lean_inc_n(v_toBind_1268_, 2);
v_toPure_1269_ = lean_ctor_get(v_toApplicative_1266_, 1);
v___x_1270_ = lean_box(0);
v___x_1271_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1269_, 2);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1272_, 0, v_toPure_1269_);
v___f_1273_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1273_, 0, v___x_1270_);
lean_closure_set(v___f_1273_, 1, v_toPure_1269_);
lean_closure_set(v___f_1273_, 2, v___x_1271_);
lean_inc_ref(v_inst_1263_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1274_, 0, v_inst_1263_);
lean_closure_set(v___f_1274_, 1, v_f_1264_);
lean_closure_set(v___f_1274_, 2, v_toBind_1268_);
lean_closure_set(v___f_1274_, 3, v___f_1273_);
v_sz_1275_ = lean_array_size(v_cs_1267_);
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1263_, v_cs_1267_, v___f_1274_, v_sz_1275_, v___x_1276_, v___x_1271_);
v___x_1278_ = lean_apply_4(v_toBind_1268_, lean_box(0), lean_box(0), v___x_1277_, v___f_1272_);
return v___x_1278_;
}
else
{
lean_object* v_toApplicative_1279_; lean_object* v_vs_1280_; lean_object* v_toBind_1281_; lean_object* v_toPure_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; size_t v_sz_1288_; size_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_toApplicative_1279_ = lean_ctor_get(v_inst_1263_, 0);
v_vs_1280_ = lean_ctor_get(v_x_1265_, 0);
lean_inc_ref(v_vs_1280_);
lean_dec_ref_known(v_x_1265_, 1);
v_toBind_1281_ = lean_ctor_get(v_inst_1263_, 1);
lean_inc_n(v_toBind_1281_, 2);
v_toPure_1282_ = lean_ctor_get(v_toApplicative_1279_, 1);
v___x_1283_ = lean_box(0);
v___x_1284_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1282_, 2);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1285_, 0, v_toPure_1282_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1286_, 0, v___x_1283_);
lean_closure_set(v___f_1286_, 1, v_toPure_1282_);
lean_closure_set(v___f_1286_, 2, v___x_1284_);
v___f_1287_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1287_, 0, v_f_1264_);
lean_closure_set(v___f_1287_, 1, v_toBind_1281_);
lean_closure_set(v___f_1287_, 2, v___f_1286_);
v_sz_1288_ = lean_array_size(v_vs_1280_);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1263_, v_vs_1280_, v___f_1287_, v_sz_1288_, v___x_1289_, v___x_1284_);
v___x_1291_ = lean_apply_4(v_toBind_1281_, lean_box(0), lean_box(0), v___x_1290_, v___f_1285_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1292_, lean_object* v_f_1293_, lean_object* v_toBind_1294_, lean_object* v___f_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1292_, v_f_1293_, v_a_1296_);
v___x_1300_ = lean_apply_4(v_toBind_1294_, lean_box(0), lean_box(0), v___x_1299_, v___f_1295_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1301_, lean_object* v_m_1302_, lean_object* v_inst_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_f_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1303_, v_f_1305_, v_x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1308_, lean_object* v_____do__lift_1309_, lean_object* v_____s_1310_){
_start:
{
lean_object* v_fst_1311_; 
v_fst_1311_ = lean_ctor_get(v_____s_1310_, 0);
lean_inc(v_fst_1311_);
lean_dec_ref(v_____s_1310_);
if (lean_obj_tag(v_fst_1311_) == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_apply_2(v_toPure_1308_, lean_box(0), v_____do__lift_1309_);
return v___x_1312_;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; 
lean_dec(v_____do__lift_1309_);
v_val_1313_ = lean_ctor_get(v_fst_1311_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v_fst_1311_, 1);
v___x_1314_ = lean_apply_2(v_toPure_1308_, lean_box(0), v_val_1313_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1315_, lean_object* v_toPure_1316_, lean_object* v___x_1317_, lean_object* v_____do__lift_1318_){
_start:
{
if (lean_obj_tag(v_____do__lift_1318_) == 1)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v___x_1317_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_____do__lift_1318_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1315_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___x_1322_ = lean_apply_2(v_toPure_1316_, lean_box(0), v___x_1321_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_____do__lift_1318_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1317_);
v___x_1324_ = lean_apply_2(v_toPure_1316_, lean_box(0), v___x_1323_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1325_, lean_object* v_toBind_1326_, lean_object* v___f_1327_, lean_object* v_a_1328_, lean_object* v_x_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_apply_1(v_f_1325_, v_a_1328_);
v___x_1332_ = lean_apply_4(v_toBind_1326_, lean_box(0), lean_box(0), v___x_1331_, v___f_1327_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1333_, lean_object* v_toBind_1334_, lean_object* v___f_1335_, lean_object* v_a_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1333_, v_toBind_1334_, v___f_1335_, v_a_1336_, v_x_1337_, v___y_1338_);
lean_dec_ref(v___y_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1340_, lean_object* v_f_1341_, lean_object* v_toBind_1342_, lean_object* v_tail_1343_, lean_object* v_inst_1344_, lean_object* v_____do__lift_1345_){
_start:
{
if (lean_obj_tag(v_____do__lift_1345_) == 0)
{
lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; lean_object* v___f_1350_; size_t v_sz_1351_; size_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_inc(v_toPure_1340_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1346_, 0, v_toPure_1340_);
lean_closure_set(v___f_1346_, 1, v_____do__lift_1345_);
v___x_1347_ = lean_box(0);
v___x_1348_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1349_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1349_, 0, v___x_1347_);
lean_closure_set(v___f_1349_, 1, v_toPure_1340_);
lean_closure_set(v___f_1349_, 2, v___x_1348_);
lean_inc(v_toBind_1342_);
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1350_, 0, v_f_1341_);
lean_closure_set(v___f_1350_, 1, v_toBind_1342_);
lean_closure_set(v___f_1350_, 2, v___f_1349_);
v_sz_1351_ = lean_array_size(v_tail_1343_);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1344_, v_tail_1343_, v___f_1350_, v_sz_1351_, v___x_1352_, v___x_1348_);
v___x_1354_ = lean_apply_4(v_toBind_1342_, lean_box(0), lean_box(0), v___x_1353_, v___f_1346_);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; 
lean_dec_ref(v_inst_1344_);
lean_dec_ref(v_tail_1343_);
lean_dec(v_toBind_1342_);
lean_dec(v_f_1341_);
v___x_1355_ = lean_apply_2(v_toPure_1340_, lean_box(0), v_____do__lift_1345_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1356_, lean_object* v_t_1357_, lean_object* v_f_1358_){
_start:
{
lean_object* v_toApplicative_1359_; lean_object* v_toBind_1360_; lean_object* v_root_1361_; lean_object* v_tail_1362_; lean_object* v_toPure_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; 
v_toApplicative_1359_ = lean_ctor_get(v_inst_1356_, 0);
v_toBind_1360_ = lean_ctor_get(v_inst_1356_, 1);
lean_inc_n(v_toBind_1360_, 2);
v_root_1361_ = lean_ctor_get(v_t_1357_, 0);
lean_inc_ref(v_root_1361_);
v_tail_1362_ = lean_ctor_get(v_t_1357_, 1);
lean_inc_ref(v_tail_1362_);
lean_dec_ref(v_t_1357_);
v_toPure_1363_ = lean_ctor_get(v_toApplicative_1359_, 1);
lean_inc(v_toPure_1363_);
lean_inc(v_f_1358_);
lean_inc_ref(v_inst_1356_);
v___x_1364_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1356_, v_f_1358_, v_root_1361_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1365_, 0, v_toPure_1363_);
lean_closure_set(v___f_1365_, 1, v_f_1358_);
lean_closure_set(v___f_1365_, 2, v_toBind_1360_);
lean_closure_set(v___f_1365_, 3, v_tail_1362_);
lean_closure_set(v___f_1365_, 4, v_inst_1356_);
v___x_1366_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1364_, v___f_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1367_, lean_object* v_m_1368_, lean_object* v_inst_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_t_1371_, lean_object* v_f_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1369_, v_t_1371_, v_f_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1374_, lean_object* v_f_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v_cs_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_cs_1377_ = lean_ctor_get(v_x_1376_, 0);
lean_inc_ref(v_cs_1377_);
lean_dec_ref_known(v_x_1376_, 1);
lean_inc_ref(v_inst_1374_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1378_, 0, v_inst_1374_);
lean_closure_set(v___f_1378_, 1, v_f_1375_);
v___x_1379_ = lean_array_get_size(v_cs_1377_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1374_, v___f_1378_, v_cs_1377_, v___x_1379_, lean_box(0));
return v___x_1380_;
}
else
{
lean_object* v_vs_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_vs_1381_ = lean_ctor_get(v_x_1376_, 0);
lean_inc_ref(v_vs_1381_);
lean_dec_ref_known(v_x_1376_, 1);
v___x_1382_ = lean_array_get_size(v_vs_1381_);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1374_, v_f_1375_, v_vs_1381_, v___x_1382_, lean_box(0));
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1384_, lean_object* v_f_1385_, lean_object* v_c_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1384_, v_f_1385_, v_c_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1388_, lean_object* v_m_1389_, lean_object* v_inst_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_f_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1390_, v_f_1392_, v_x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1395_, lean_object* v_f_1396_, lean_object* v_root_1397_, lean_object* v_toPure_1398_, lean_object* v_____do__lift_1399_){
_start:
{
if (lean_obj_tag(v_____do__lift_1399_) == 0)
{
lean_object* v___x_1400_; 
lean_dec(v_toPure_1398_);
v___x_1400_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1395_, v_f_1396_, v_root_1397_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v_root_1397_);
lean_dec(v_f_1396_);
lean_dec_ref(v_inst_1395_);
v___x_1401_ = lean_apply_2(v_toPure_1398_, lean_box(0), v_____do__lift_1399_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1402_, lean_object* v_t_1403_, lean_object* v_f_1404_){
_start:
{
lean_object* v_toApplicative_1405_; lean_object* v_toBind_1406_; lean_object* v_root_1407_; lean_object* v_tail_1408_; lean_object* v_toPure_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1402_, 0);
v_toBind_1406_ = lean_ctor_get(v_inst_1402_, 1);
lean_inc(v_toBind_1406_);
v_root_1407_ = lean_ctor_get(v_t_1403_, 0);
lean_inc_ref(v_root_1407_);
v_tail_1408_ = lean_ctor_get(v_t_1403_, 1);
lean_inc_ref(v_tail_1408_);
lean_dec_ref(v_t_1403_);
v_toPure_1409_ = lean_ctor_get(v_toApplicative_1405_, 1);
lean_inc(v_toPure_1409_);
v___x_1410_ = lean_array_get_size(v_tail_1408_);
lean_inc(v_f_1404_);
lean_inc_ref(v_inst_1402_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1402_, v_f_1404_, v_tail_1408_, v___x_1410_, lean_box(0));
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1412_, 0, v_inst_1402_);
lean_closure_set(v___f_1412_, 1, v_f_1404_);
lean_closure_set(v___f_1412_, 2, v_root_1407_);
lean_closure_set(v___f_1412_, 3, v_toPure_1409_);
v___x_1413_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1411_, v___f_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1414_, lean_object* v_m_1415_, lean_object* v_inst_1416_, lean_object* v_00_u03b2_1417_, lean_object* v_t_1418_, lean_object* v_f_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1416_, v_t_1418_, v_f_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_apply_1(v_f_1421_, v___y_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1425_, lean_object* v_f_1426_, lean_object* v_x_1427_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_object* v_toApplicative_1428_; lean_object* v_cs_1429_; lean_object* v_toPure_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_toApplicative_1428_ = lean_ctor_get(v_inst_1425_, 0);
v_cs_1429_ = lean_ctor_get(v_x_1427_, 0);
lean_inc_ref(v_cs_1429_);
lean_dec_ref_known(v_x_1427_, 1);
v_toPure_1430_ = lean_ctor_get(v_toApplicative_1428_, 1);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_array_get_size(v_cs_1429_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_nat_dec_lt(v___x_1431_, v___x_1432_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_inc(v_toPure_1430_);
lean_dec_ref(v_cs_1429_);
lean_dec(v_f_1426_);
lean_dec_ref(v_inst_1425_);
v___x_1435_ = lean_apply_2(v_toPure_1430_, lean_box(0), v___x_1433_);
return v___x_1435_;
}
else
{
lean_object* v___f_1436_; size_t v___x_1437_; size_t v___x_1438_; lean_object* v___x_1439_; 
lean_inc_ref(v_inst_1425_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1436_, 0, v_inst_1425_);
lean_closure_set(v___f_1436_, 1, v_f_1426_);
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = lean_usize_of_nat(v___x_1432_);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1425_, v___f_1436_, v_cs_1429_, v___x_1437_, v___x_1438_, v___x_1433_);
return v___x_1439_;
}
}
else
{
lean_object* v_toApplicative_1440_; lean_object* v_vs_1441_; lean_object* v_toPure_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_toApplicative_1440_ = lean_ctor_get(v_inst_1425_, 0);
v_vs_1441_ = lean_ctor_get(v_x_1427_, 0);
lean_inc_ref(v_vs_1441_);
lean_dec_ref_known(v_x_1427_, 1);
v_toPure_1442_ = lean_ctor_get(v_toApplicative_1440_, 1);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_array_get_size(v_vs_1441_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_nat_dec_lt(v___x_1443_, v___x_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_inc(v_toPure_1442_);
lean_dec_ref(v_vs_1441_);
lean_dec(v_f_1426_);
lean_dec_ref(v_inst_1425_);
v___x_1447_ = lean_apply_2(v_toPure_1442_, lean_box(0), v___x_1445_);
return v___x_1447_;
}
else
{
lean_object* v___f_1448_; size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1448_, 0, v_f_1426_);
v___x_1449_ = ((size_t)0ULL);
v___x_1450_ = lean_usize_of_nat(v___x_1444_);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1425_, v___f_1448_, v_vs_1441_, v___x_1449_, v___x_1450_, v___x_1445_);
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1452_, lean_object* v_f_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1452_, v_f_1453_, v___y_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1457_, lean_object* v_m_1458_, lean_object* v_inst_1459_, lean_object* v_f_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1459_, v_f_1460_, v_x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1463_, lean_object* v_x_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_apply_1(v_f_1463_, v___y_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1467_, lean_object* v_toPure_1468_, lean_object* v_inst_1469_, lean_object* v___f_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_array_get_size(v_tail_1467_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_nat_dec_lt(v___x_1472_, v___x_1473_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec(v___f_1470_);
lean_dec_ref(v_inst_1469_);
lean_dec_ref(v_tail_1467_);
v___x_1476_ = lean_apply_2(v_toPure_1468_, lean_box(0), v___x_1474_);
return v___x_1476_;
}
else
{
size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_toPure_1468_);
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = lean_usize_of_nat(v___x_1473_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1469_, v___f_1470_, v_tail_1467_, v___x_1477_, v___x_1478_, v___x_1474_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1480_, lean_object* v_t_1481_, lean_object* v_f_1482_){
_start:
{
lean_object* v_toApplicative_1483_; lean_object* v_toPure_1484_; lean_object* v_toSeqRight_1485_; lean_object* v_root_1486_; lean_object* v_tail_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toApplicative_1483_ = lean_ctor_get(v_inst_1480_, 0);
v_toPure_1484_ = lean_ctor_get(v_toApplicative_1483_, 1);
v_toSeqRight_1485_ = lean_ctor_get(v_toApplicative_1483_, 4);
lean_inc(v_toSeqRight_1485_);
v_root_1486_ = lean_ctor_get(v_t_1481_, 0);
lean_inc_ref(v_root_1486_);
v_tail_1487_ = lean_ctor_get(v_t_1481_, 1);
lean_inc_ref(v_tail_1487_);
lean_dec_ref(v_t_1481_);
lean_inc(v_f_1482_);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1488_, 0, v_f_1482_);
lean_inc_ref(v_inst_1480_);
lean_inc(v_toPure_1484_);
v___f_1489_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1489_, 0, v_tail_1487_);
lean_closure_set(v___f_1489_, 1, v_toPure_1484_);
lean_closure_set(v___f_1489_, 2, v_inst_1480_);
lean_closure_set(v___f_1489_, 3, v___f_1488_);
v___x_1490_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1480_, v_f_1482_, v_root_1486_);
v___x_1491_ = lean_apply_4(v_toSeqRight_1485_, lean_box(0), lean_box(0), v___x_1490_, v___f_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1492_, lean_object* v_m_1493_, lean_object* v_inst_1494_, lean_object* v_t_1495_, lean_object* v_f_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1494_, v_t_1495_, v_f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_toApplicative_1498_, lean_object* v_j_1499_, lean_object* v_cs_1500_, lean_object* v_inst_1501_, lean_object* v___f_1502_, lean_object* v_____r_1503_){
_start:
{
lean_object* v_toPure_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_toPure_1504_ = lean_ctor_get(v_toApplicative_1498_, 1);
lean_inc(v_toPure_1504_);
lean_dec_ref(v_toApplicative_1498_);
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_nat_add(v_j_1499_, v___x_1505_);
v___x_1507_ = lean_array_get_size(v_cs_1500_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec(v___x_1506_);
lean_dec(v___f_1502_);
lean_dec_ref(v_inst_1501_);
lean_dec_ref(v_cs_1500_);
v___x_1510_ = lean_apply_2(v_toPure_1504_, lean_box(0), v___x_1508_);
return v___x_1510_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_toPure_1504_);
v___x_1511_ = lean_usize_of_nat(v___x_1506_);
lean_dec(v___x_1506_);
v___x_1512_ = lean_usize_of_nat(v___x_1507_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1501_, v___f_1502_, v_cs_1500_, v___x_1511_, v___x_1512_, v___x_1508_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_1514_, lean_object* v_j_1515_, lean_object* v_cs_1516_, lean_object* v_inst_1517_, lean_object* v___f_1518_, lean_object* v_____r_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_toApplicative_1514_, v_j_1515_, v_cs_1516_, v_inst_1517_, v___f_1518_, v_____r_1519_);
lean_dec(v_j_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1521_, lean_object* v_f_1522_, lean_object* v_x_1523_, size_t v_x_1524_, size_t v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1523_) == 0)
{
lean_object* v_toApplicative_1526_; lean_object* v_toBind_1527_; lean_object* v_cs_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; size_t v___x_1531_; lean_object* v_j_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_toApplicative_1526_ = lean_ctor_get(v_inst_1521_, 0);
v_toBind_1527_ = lean_ctor_get(v_inst_1521_, 1);
lean_inc(v_toBind_1527_);
v_cs_1528_ = lean_ctor_get(v_x_1523_, 0);
lean_inc_ref_n(v_cs_1528_, 2);
lean_dec_ref_known(v_x_1523_, 1);
lean_inc(v_f_1522_);
lean_inc_ref_n(v_inst_1521_, 2);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1529_, 0, v_inst_1521_);
lean_closure_set(v___f_1529_, 1, v_f_1522_);
v___x_1530_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1531_ = lean_usize_shift_right(v_x_1524_, v_x_1525_);
v_j_1532_ = lean_usize_to_nat(v___x_1531_);
lean_inc(v_j_1532_);
lean_inc_ref(v_toApplicative_1526_);
v___f_1533_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1533_, 0, v_toApplicative_1526_);
lean_closure_set(v___f_1533_, 1, v_j_1532_);
lean_closure_set(v___f_1533_, 2, v_cs_1528_);
lean_closure_set(v___f_1533_, 3, v_inst_1521_);
lean_closure_set(v___f_1533_, 4, v___f_1529_);
v___x_1534_ = lean_array_get(v___x_1530_, v_cs_1528_, v_j_1532_);
lean_dec(v_j_1532_);
lean_dec_ref(v_cs_1528_);
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_shift_left(v___x_1535_, v_x_1525_);
v___x_1537_ = lean_usize_sub(v___x_1536_, v___x_1535_);
v___x_1538_ = lean_usize_land(v_x_1524_, v___x_1537_);
v___x_1539_ = ((size_t)5ULL);
v___x_1540_ = lean_usize_sub(v_x_1525_, v___x_1539_);
v___x_1541_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1521_, v_f_1522_, v___x_1534_, v___x_1538_, v___x_1540_);
v___x_1542_ = lean_apply_4(v_toBind_1527_, lean_box(0), lean_box(0), v___x_1541_, v___f_1533_);
return v___x_1542_;
}
else
{
lean_object* v_toApplicative_1543_; lean_object* v_vs_1544_; lean_object* v_toPure_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_toApplicative_1543_ = lean_ctor_get(v_inst_1521_, 0);
v_vs_1544_ = lean_ctor_get(v_x_1523_, 0);
lean_inc_ref(v_vs_1544_);
lean_dec_ref_known(v_x_1523_, 1);
v_toPure_1545_ = lean_ctor_get(v_toApplicative_1543_, 1);
v___x_1546_ = lean_usize_to_nat(v_x_1524_);
v___x_1547_ = lean_array_get_size(v_vs_1544_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_nat_dec_lt(v___x_1546_, v___x_1547_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_inc(v_toPure_1545_);
lean_dec(v___x_1546_);
lean_dec_ref(v_vs_1544_);
lean_dec(v_f_1522_);
lean_dec_ref(v_inst_1521_);
v___x_1550_ = lean_apply_2(v_toPure_1545_, lean_box(0), v___x_1548_);
return v___x_1550_;
}
else
{
lean_object* v___f_1551_; size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1551_, 0, v_f_1522_);
v___x_1552_ = lean_usize_of_nat(v___x_1546_);
lean_dec(v___x_1546_);
v___x_1553_ = lean_usize_of_nat(v___x_1547_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1521_, v___f_1551_, v_vs_1544_, v___x_1552_, v___x_1553_, v___x_1548_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1555_, lean_object* v_f_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
size_t v_x_257__boxed_1560_; size_t v_x_258__boxed_1561_; lean_object* v_res_1562_; 
v_x_257__boxed_1560_ = lean_unbox_usize(v_x_1558_);
lean_dec(v_x_1558_);
v_x_258__boxed_1561_ = lean_unbox_usize(v_x_1559_);
lean_dec(v_x_1559_);
v_res_1562_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1555_, v_f_1556_, v_x_1557_, v_x_257__boxed_1560_, v_x_258__boxed_1561_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1563_, lean_object* v_m_1564_, lean_object* v_inst_1565_, lean_object* v_f_1566_, lean_object* v_x_1567_, size_t v_x_1568_, size_t v_x_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1565_, v_f_1566_, v_x_1567_, v_x_1568_, v_x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_m_1572_, lean_object* v_inst_1573_, lean_object* v_f_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
size_t v_x_317__boxed_1578_; size_t v_x_318__boxed_1579_; lean_object* v_res_1580_; 
v_x_317__boxed_1578_ = lean_unbox_usize(v_x_1576_);
lean_dec(v_x_1576_);
v_x_318__boxed_1579_ = lean_unbox_usize(v_x_1577_);
lean_dec(v_x_1577_);
v_res_1580_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1571_, v_m_1572_, v_inst_1573_, v_f_1574_, v_x_1575_, v_x_317__boxed_1578_, v_x_318__boxed_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_toApplicative_1581_, lean_object* v_tail_1582_, lean_object* v___x_1583_, lean_object* v_inst_1584_, lean_object* v___f_1585_, lean_object* v_____r_1586_){
_start:
{
lean_object* v_toPure_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_toPure_1587_ = lean_ctor_get(v_toApplicative_1581_, 1);
lean_inc(v_toPure_1587_);
lean_dec_ref(v_toApplicative_1581_);
v___x_1588_ = lean_array_get_size(v_tail_1582_);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_nat_dec_lt(v___x_1583_, v___x_1588_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_dec(v___f_1585_);
lean_dec_ref(v_inst_1584_);
lean_dec_ref(v_tail_1582_);
v___x_1591_ = lean_apply_2(v_toPure_1587_, lean_box(0), v___x_1589_);
return v___x_1591_;
}
else
{
size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_toPure_1587_);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = lean_usize_of_nat(v___x_1588_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1584_, v___f_1585_, v_tail_1582_, v___x_1592_, v___x_1593_, v___x_1589_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_toApplicative_1595_, lean_object* v_tail_1596_, lean_object* v___x_1597_, lean_object* v_inst_1598_, lean_object* v___f_1599_, lean_object* v_____r_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_toApplicative_1595_, v_tail_1596_, v___x_1597_, v_inst_1598_, v___f_1599_, v_____r_1600_);
lean_dec(v___x_1597_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1602_, lean_object* v_t_1603_, lean_object* v_f_1604_, lean_object* v_start_1605_){
_start:
{
lean_object* v_toApplicative_1606_; lean_object* v_toBind_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_toApplicative_1606_ = lean_ctor_get(v_inst_1602_, 0);
v_toBind_1607_ = lean_ctor_get(v_inst_1602_, 1);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_nat_dec_eq(v_start_1605_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v_root_1610_; lean_object* v_tail_1611_; size_t v_shift_1612_; lean_object* v_tailOff_1613_; uint8_t v___x_1614_; 
v_root_1610_ = lean_ctor_get(v_t_1603_, 0);
lean_inc_ref(v_root_1610_);
v_tail_1611_ = lean_ctor_get(v_t_1603_, 1);
lean_inc_ref(v_tail_1611_);
v_shift_1612_ = lean_ctor_get_usize(v_t_1603_, 4);
v_tailOff_1613_ = lean_ctor_get(v_t_1603_, 3);
lean_inc(v_tailOff_1613_);
lean_dec_ref(v_t_1603_);
v___x_1614_ = lean_nat_dec_le(v_tailOff_1613_, v_start_1605_);
if (v___x_1614_ == 0)
{
lean_object* v___f_1615_; lean_object* v___f_1616_; size_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_inc(v_toBind_1607_);
lean_dec(v_tailOff_1613_);
lean_inc(v_f_1604_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1615_, 0, v_f_1604_);
lean_inc_ref(v_inst_1602_);
lean_inc_ref(v_toApplicative_1606_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1616_, 0, v_toApplicative_1606_);
lean_closure_set(v___f_1616_, 1, v_tail_1611_);
lean_closure_set(v___f_1616_, 2, v___x_1608_);
lean_closure_set(v___f_1616_, 3, v_inst_1602_);
lean_closure_set(v___f_1616_, 4, v___f_1615_);
v___x_1617_ = lean_usize_of_nat(v_start_1605_);
v___x_1618_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1602_, v_f_1604_, v_root_1610_, v___x_1617_, v_shift_1612_);
v___x_1619_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1618_, v___f_1616_);
return v___x_1619_;
}
else
{
lean_object* v_toPure_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
lean_dec_ref(v_root_1610_);
v_toPure_1620_ = lean_ctor_get(v_toApplicative_1606_, 1);
v___x_1621_ = lean_nat_sub(v_start_1605_, v_tailOff_1613_);
lean_dec(v_tailOff_1613_);
v___x_1622_ = lean_array_get_size(v_tail_1611_);
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_nat_dec_lt(v___x_1621_, v___x_1622_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_inc(v_toPure_1620_);
lean_dec(v___x_1621_);
lean_dec_ref(v_tail_1611_);
lean_dec(v_f_1604_);
lean_dec_ref(v_inst_1602_);
v___x_1625_ = lean_apply_2(v_toPure_1620_, lean_box(0), v___x_1623_);
return v___x_1625_;
}
else
{
lean_object* v___f_1626_; size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1626_, 0, v_f_1604_);
v___x_1627_ = lean_usize_of_nat(v___x_1621_);
lean_dec(v___x_1621_);
v___x_1628_ = lean_usize_of_nat(v___x_1622_);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1602_, v___f_1626_, v_tail_1611_, v___x_1627_, v___x_1628_, v___x_1623_);
return v___x_1629_;
}
}
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1602_, v_t_1603_, v_f_1604_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1631_, lean_object* v_t_1632_, lean_object* v_f_1633_, lean_object* v_start_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_PersistentArray_forM___redArg(v_inst_1631_, v_t_1632_, v_f_1633_, v_start_1634_);
lean_dec(v_start_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1636_, lean_object* v_m_1637_, lean_object* v_inst_1638_, lean_object* v_t_1639_, lean_object* v_f_1640_, lean_object* v_start_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_PersistentArray_forM___redArg(v_inst_1638_, v_t_1639_, v_f_1640_, v_start_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_m_1644_, lean_object* v_inst_1645_, lean_object* v_t_1646_, lean_object* v_f_1647_, lean_object* v_start_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_PersistentArray_forM(v_00_u03b1_1643_, v_m_1644_, v_inst_1645_, v_t_1646_, v_f_1647_, v_start_1648_);
lean_dec(v_start_1648_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1650_, lean_object* v_x1_1651_, lean_object* v_x2_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_apply_2(v_f_1650_, v_x1_1651_, v_x2_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1673_, lean_object* v_f_1674_, lean_object* v_init_1675_, lean_object* v_start_1676_){
_start:
{
lean_object* v___f_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1677_, 0, v_f_1674_);
v___x_1678_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1679_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1678_, v_t_1673_, v___f_1677_, v_init_1675_, v_start_1676_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1680_, lean_object* v_f_1681_, lean_object* v_init_1682_, lean_object* v_start_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_PersistentArray_foldl___redArg(v_t_1680_, v_f_1681_, v_init_1682_, v_start_1683_);
lean_dec(v_start_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_t_1687_, lean_object* v_f_1688_, lean_object* v_init_1689_, lean_object* v_start_1690_){
_start:
{
lean_object* v___f_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1691_, 0, v_f_1688_);
v___x_1692_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1693_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1692_, v_t_1687_, v___f_1691_, v_init_1689_, v_start_1690_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_00_u03b2_1695_, lean_object* v_t_1696_, lean_object* v_f_1697_, lean_object* v_init_1698_, lean_object* v_start_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1694_, v_00_u03b2_1695_, v_t_1696_, v_f_1697_, v_init_1698_, v_start_1699_);
lean_dec(v_start_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1701_, lean_object* v_f_1702_, lean_object* v_init_1703_){
_start:
{
lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1704_, 0, v_f_1702_);
v___x_1705_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1706_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1705_, v_t_1701_, v___f_1704_, v_init_1703_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1707_, lean_object* v_00_u03b2_1708_, lean_object* v_t_1709_, lean_object* v_f_1710_, lean_object* v_init_1711_){
_start:
{
lean_object* v___f_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1712_, 0, v_f_1710_);
v___x_1713_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1714_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1713_, v_t_1709_, v___f_1712_, v_init_1711_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1715_, lean_object* v_x1_1716_, lean_object* v_x2_1717_){
_start:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
lean_inc(v_x2_1717_);
v___x_1718_ = lean_apply_1(v_p_1715_, v_x2_1717_);
v___x_1719_ = lean_unbox(v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec(v_x2_1717_);
return v_x1_1716_;
}
else
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_PersistentArray_push___redArg(v_x1_1716_, v_x2_1717_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1721_, lean_object* v_p_1722_){
_start:
{
lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1723_, 0, v_p_1722_);
v___x_1724_ = lean_unsigned_to_nat(32u);
v___x_1725_ = lean_mk_empty_array_with_capacity(v___x_1724_);
lean_dec_ref(v___x_1725_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1728_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1729_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1728_, v_as_1721_, v___f_1723_, v___x_1727_, v___x_1726_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1730_, lean_object* v_as_1731_, lean_object* v_p_1732_){
_start:
{
lean_object* v___f_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___f_1733_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1733_, 0, v_p_1732_);
v___x_1734_ = lean_unsigned_to_nat(32u);
v___x_1735_ = lean_mk_empty_array_with_capacity(v___x_1734_);
lean_dec_ref(v___x_1735_);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1738_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1739_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1738_, v_as_1731_, v___f_1733_, v___x_1737_, v___x_1736_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1740_, size_t v_i_1741_, size_t v_stop_1742_, lean_object* v_b_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_eq(v_i_1741_, v_stop_1742_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; 
v___x_1745_ = lean_array_uget_borrowed(v_as_1740_, v_i_1741_);
lean_inc(v___x_1745_);
v___x_1746_ = lean_array_push(v_b_1743_, v___x_1745_);
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1741_, v___x_1747_);
v_i_1741_ = v___x_1748_;
v_b_1743_ = v___x_1746_;
goto _start;
}
else
{
return v_b_1743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v_stop_1752_, lean_object* v_b_1753_){
_start:
{
size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; lean_object* v_res_1756_; 
v_i_boxed_1754_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1752_);
lean_dec(v_stop_1752_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1750_, v_i_boxed_1754_, v_stop_boxed_1755_, v_b_1753_);
lean_dec_ref(v_as_1750_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1757_) == 0)
{
lean_object* v_cs_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_cs_1759_ = lean_ctor_get(v_x_1757_, 0);
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_array_get_size(v_cs_1759_);
v___x_1762_ = lean_nat_dec_lt(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
return v_x_1758_;
}
else
{
size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = lean_usize_of_nat(v___x_1761_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1759_, v___x_1763_, v___x_1764_, v_x_1758_);
return v___x_1765_;
}
}
else
{
lean_object* v_vs_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_vs_1766_ = lean_ctor_get(v_x_1757_, 0);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_array_get_size(v_vs_1766_);
v___x_1769_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
return v_x_1758_;
}
else
{
size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((size_t)0ULL);
v___x_1771_ = lean_usize_of_nat(v___x_1768_);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1766_, v___x_1770_, v___x_1771_, v_x_1758_);
return v___x_1772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1773_, size_t v_i_1774_, size_t v_stop_1775_, lean_object* v_b_1776_){
_start:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_eq(v_i_1774_, v_stop_1775_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; size_t v___x_1780_; size_t v___x_1781_; 
v___x_1778_ = lean_array_uget_borrowed(v_as_1773_, v_i_1774_);
v___x_1779_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1778_, v_b_1776_);
v___x_1780_ = ((size_t)1ULL);
v___x_1781_ = lean_usize_add(v_i_1774_, v___x_1780_);
v_i_1774_ = v___x_1781_;
v_b_1776_ = v___x_1779_;
goto _start;
}
else
{
return v_b_1776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1783_, lean_object* v_i_1784_, lean_object* v_stop_1785_, lean_object* v_b_1786_){
_start:
{
size_t v_i_boxed_1787_; size_t v_stop_boxed_1788_; lean_object* v_res_1789_; 
v_i_boxed_1787_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_stop_boxed_1788_ = lean_unbox_usize(v_stop_1785_);
lean_dec(v_stop_1785_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1783_, v_i_boxed_1787_, v_stop_boxed_1788_, v_b_1786_);
lean_dec_ref(v_as_1783_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1790_, v_x_1791_);
lean_dec_ref(v_x_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1793_, size_t v_x_1794_, size_t v_x_1795_, lean_object* v_x_1796_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
lean_object* v_cs_1797_; lean_object* v___x_1798_; size_t v___x_1799_; lean_object* v_j_1800_; lean_object* v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_cs_1797_ = lean_ctor_get(v_x_1793_, 0);
v___x_1798_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1799_ = lean_usize_shift_right(v_x_1794_, v_x_1795_);
v_j_1800_ = lean_usize_to_nat(v___x_1799_);
v___x_1801_ = lean_array_get_borrowed(v___x_1798_, v_cs_1797_, v_j_1800_);
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_shift_left(v___x_1802_, v_x_1795_);
v___x_1804_ = lean_usize_sub(v___x_1803_, v___x_1802_);
v___x_1805_ = lean_usize_land(v_x_1794_, v___x_1804_);
v___x_1806_ = ((size_t)5ULL);
v___x_1807_ = lean_usize_sub(v_x_1795_, v___x_1806_);
v___x_1808_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1801_, v___x_1805_, v___x_1807_, v_x_1796_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_add(v_j_1800_, v___x_1809_);
lean_dec(v_j_1800_);
v___x_1811_ = lean_array_get_size(v_cs_1797_);
v___x_1812_ = lean_nat_dec_lt(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec(v___x_1810_);
return v___x_1808_;
}
else
{
size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_usize_of_nat(v___x_1810_);
lean_dec(v___x_1810_);
v___x_1814_ = lean_usize_of_nat(v___x_1811_);
v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1797_, v___x_1813_, v___x_1814_, v___x_1808_);
return v___x_1815_;
}
}
else
{
lean_object* v_vs_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_vs_1816_ = lean_ctor_get(v_x_1793_, 0);
v___x_1817_ = lean_usize_to_nat(v_x_1794_);
v___x_1818_ = lean_array_get_size(v_vs_1816_);
v___x_1819_ = lean_nat_dec_lt(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_dec(v___x_1817_);
return v_x_1796_;
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_usize_of_nat(v___x_1817_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_usize_of_nat(v___x_1818_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1816_, v___x_1820_, v___x_1821_, v_x_1796_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_){
_start:
{
size_t v_x_1118__boxed_1827_; size_t v_x_1119__boxed_1828_; lean_object* v_res_1829_; 
v_x_1118__boxed_1827_ = lean_unbox_usize(v_x_1824_);
lean_dec(v_x_1824_);
v_x_1119__boxed_1828_ = lean_unbox_usize(v_x_1825_);
lean_dec(v_x_1825_);
v_res_1829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1823_, v_x_1118__boxed_1827_, v_x_1119__boxed_1828_, v_x_1826_);
lean_dec_ref(v_x_1823_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1830_, lean_object* v_init_1831_, lean_object* v_start_1832_){
_start:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = lean_nat_dec_eq(v_start_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v_root_1835_; lean_object* v_tail_1836_; size_t v_shift_1837_; lean_object* v_tailOff_1838_; uint8_t v___x_1839_; 
v_root_1835_ = lean_ctor_get(v_t_1830_, 0);
v_tail_1836_ = lean_ctor_get(v_t_1830_, 1);
v_shift_1837_ = lean_ctor_get_usize(v_t_1830_, 4);
v_tailOff_1838_ = lean_ctor_get(v_t_1830_, 3);
v___x_1839_ = lean_nat_dec_le(v_tailOff_1838_, v_start_1832_);
if (v___x_1839_ == 0)
{
size_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1840_ = lean_usize_of_nat(v_start_1832_);
v___x_1841_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1835_, v___x_1840_, v_shift_1837_, v_init_1831_);
v___x_1842_ = lean_array_get_size(v_tail_1836_);
v___x_1843_ = lean_nat_dec_lt(v___x_1833_, v___x_1842_);
if (v___x_1843_ == 0)
{
return v___x_1841_;
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1842_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1836_, v___x_1844_, v___x_1845_, v___x_1841_);
return v___x_1846_;
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = lean_nat_sub(v_start_1832_, v_tailOff_1838_);
v___x_1848_ = lean_array_get_size(v_tail_1836_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec(v___x_1847_);
return v_init_1831_;
}
else
{
size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_usize_of_nat(v___x_1847_);
lean_dec(v___x_1847_);
v___x_1851_ = lean_usize_of_nat(v___x_1848_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1836_, v___x_1850_, v___x_1851_, v_init_1831_);
return v___x_1852_;
}
}
}
else
{
lean_object* v_root_1853_; lean_object* v_tail_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v_root_1853_ = lean_ctor_get(v_t_1830_, 0);
v_tail_1854_ = lean_ctor_get(v_t_1830_, 1);
v___x_1855_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1853_, v_init_1831_);
v___x_1856_ = lean_array_get_size(v_tail_1854_);
v___x_1857_ = lean_nat_dec_lt(v___x_1833_, v___x_1856_);
if (v___x_1857_ == 0)
{
return v___x_1855_;
}
else
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_of_nat(v___x_1856_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1854_, v___x_1858_, v___x_1859_, v___x_1855_);
return v___x_1860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1861_, lean_object* v_init_1862_, lean_object* v_start_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1861_, v_init_1862_, v_start_1863_);
lean_dec(v_start_1863_);
lean_dec_ref(v_t_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1868_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1865_, v___x_1867_, v___x_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_PersistentArray_toArray___redArg(v_t_1869_);
lean_dec_ref(v_t_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1871_, lean_object* v_t_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_PersistentArray_toArray___redArg(v_t_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_t_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1874_, v_t_1875_);
lean_dec_ref(v_t_1875_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1877_, lean_object* v_t_1878_, lean_object* v_init_1879_, lean_object* v_start_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1878_, v_init_1879_, v_start_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_t_1883_, lean_object* v_init_1884_, lean_object* v_start_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1882_, v_t_1883_, v_init_1884_, v_start_1885_);
lean_dec(v_start_1885_);
lean_dec_ref(v_t_1883_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1887_, lean_object* v_x_1888_, size_t v_x_1889_, size_t v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1888_, v_x_1889_, v_x_1890_, v_x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
size_t v_x_1236__boxed_1898_; size_t v_x_1237__boxed_1899_; lean_object* v_res_1900_; 
v_x_1236__boxed_1898_ = lean_unbox_usize(v_x_1895_);
lean_dec(v_x_1895_);
v_x_1237__boxed_1899_ = lean_unbox_usize(v_x_1896_);
lean_dec(v_x_1896_);
v_res_1900_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1893_, v_x_1894_, v_x_1236__boxed_1898_, v_x_1237__boxed_1899_, v_x_1897_);
lean_dec_ref(v_x_1894_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1901_, lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_, lean_object* v_b_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1902_, v_i_1903_, v_stop_1904_, v_b_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1907_, lean_object* v_as_1908_, lean_object* v_i_1909_, lean_object* v_stop_1910_, lean_object* v_b_1911_){
_start:
{
size_t v_i_boxed_1912_; size_t v_stop_boxed_1913_; lean_object* v_res_1914_; 
v_i_boxed_1912_ = lean_unbox_usize(v_i_1909_);
lean_dec(v_i_1909_);
v_stop_boxed_1913_ = lean_unbox_usize(v_stop_1910_);
lean_dec(v_stop_1910_);
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1907_, v_as_1908_, v_i_boxed_1912_, v_stop_boxed_1913_, v_b_1911_);
lean_dec_ref(v_as_1908_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1916_, v_x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_1919_, v_x_1920_, v_x_1921_);
lean_dec_ref(v_x_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1923_, lean_object* v_as_1924_, size_t v_i_1925_, size_t v_stop_1926_, lean_object* v_b_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1924_, v_i_1925_, v_stop_1926_, v_b_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1929_, lean_object* v_as_1930_, lean_object* v_i_1931_, lean_object* v_stop_1932_, lean_object* v_b_1933_){
_start:
{
size_t v_i_boxed_1934_; size_t v_stop_boxed_1935_; lean_object* v_res_1936_; 
v_i_boxed_1934_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_stop_boxed_1935_ = lean_unbox_usize(v_stop_1932_);
lean_dec(v_stop_1932_);
v_res_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_1929_, v_as_1930_, v_i_boxed_1934_, v_stop_boxed_1935_, v_b_1933_);
lean_dec_ref(v_as_1930_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_1937_, size_t v_i_1938_, size_t v_stop_1939_, lean_object* v_b_1940_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_eq(v_i_1938_, v_stop_1939_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; 
v___x_1942_ = lean_array_uget_borrowed(v_as_1937_, v_i_1938_);
lean_inc(v___x_1942_);
v___x_1943_ = l_Lean_PersistentArray_push___redArg(v_b_1940_, v___x_1942_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_add(v_i_1938_, v___x_1944_);
v_i_1938_ = v___x_1945_;
v_b_1940_ = v___x_1943_;
goto _start;
}
else
{
return v_b_1940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_1947_, lean_object* v_i_1948_, lean_object* v_stop_1949_, lean_object* v_b_1950_){
_start:
{
size_t v_i_boxed_1951_; size_t v_stop_boxed_1952_; lean_object* v_res_1953_; 
v_i_boxed_1951_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_stop_boxed_1952_ = lean_unbox_usize(v_stop_1949_);
lean_dec(v_stop_1949_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_1947_, v_i_boxed_1951_, v_stop_boxed_1952_, v_b_1950_);
lean_dec_ref(v_as_1947_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
if (lean_obj_tag(v_x_1954_) == 0)
{
lean_object* v_cs_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_cs_1956_ = lean_ctor_get(v_x_1954_, 0);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v_cs_1956_);
v___x_1959_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
return v_x_1955_;
}
else
{
size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = lean_usize_of_nat(v___x_1958_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_1956_, v___x_1960_, v___x_1961_, v_x_1955_);
return v___x_1962_;
}
}
else
{
lean_object* v_vs_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_vs_1963_ = lean_ctor_get(v_x_1954_, 0);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_array_get_size(v_vs_1963_);
v___x_1966_ = lean_nat_dec_lt(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
return v_x_1955_;
}
else
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = lean_usize_of_nat(v___x_1965_);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_1963_, v___x_1967_, v___x_1968_, v_x_1955_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1970_, size_t v_i_1971_, size_t v_stop_1972_, lean_object* v_b_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_eq(v_i_1971_, v_stop_1972_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; 
v___x_1975_ = lean_array_uget_borrowed(v_as_1970_, v_i_1971_);
v___x_1976_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_1975_, v_b_1973_);
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1971_, v___x_1977_);
v_i_1971_ = v___x_1978_;
v_b_1973_ = v___x_1976_;
goto _start;
}
else
{
return v_b_1973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1980_, lean_object* v_i_1981_, lean_object* v_stop_1982_, lean_object* v_b_1983_){
_start:
{
size_t v_i_boxed_1984_; size_t v_stop_boxed_1985_; lean_object* v_res_1986_; 
v_i_boxed_1984_ = lean_unbox_usize(v_i_1981_);
lean_dec(v_i_1981_);
v_stop_boxed_1985_ = lean_unbox_usize(v_stop_1982_);
lean_dec(v_stop_1982_);
v_res_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_1980_, v_i_boxed_1984_, v_stop_boxed_1985_, v_b_1983_);
lean_dec_ref(v_as_1980_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_1987_, v_x_1988_);
lean_dec_ref(v_x_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_1990_, size_t v_x_1991_, size_t v_x_1992_, lean_object* v_x_1993_){
_start:
{
if (lean_obj_tag(v_x_1990_) == 0)
{
lean_object* v_cs_1994_; lean_object* v___x_1995_; size_t v___x_1996_; lean_object* v_j_1997_; lean_object* v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; size_t v___x_2001_; size_t v___x_2002_; size_t v___x_2003_; size_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_cs_1994_ = lean_ctor_get(v_x_1990_, 0);
v___x_1995_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1996_ = lean_usize_shift_right(v_x_1991_, v_x_1992_);
v_j_1997_ = lean_usize_to_nat(v___x_1996_);
v___x_1998_ = lean_array_get_borrowed(v___x_1995_, v_cs_1994_, v_j_1997_);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_shift_left(v___x_1999_, v_x_1992_);
v___x_2001_ = lean_usize_sub(v___x_2000_, v___x_1999_);
v___x_2002_ = lean_usize_land(v_x_1991_, v___x_2001_);
v___x_2003_ = ((size_t)5ULL);
v___x_2004_ = lean_usize_sub(v_x_1992_, v___x_2003_);
v___x_2005_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_1998_, v___x_2002_, v___x_2004_, v_x_1993_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_add(v_j_1997_, v___x_2006_);
lean_dec(v_j_1997_);
v___x_2008_ = lean_array_get_size(v_cs_1994_);
v___x_2009_ = lean_nat_dec_lt(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_dec(v___x_2007_);
return v___x_2005_;
}
else
{
size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_usize_of_nat(v___x_2007_);
lean_dec(v___x_2007_);
v___x_2011_ = lean_usize_of_nat(v___x_2008_);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_1994_, v___x_2010_, v___x_2011_, v___x_2005_);
return v___x_2012_;
}
}
else
{
lean_object* v_vs_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v_vs_2013_ = lean_ctor_get(v_x_1990_, 0);
v___x_2014_ = lean_usize_to_nat(v_x_1991_);
v___x_2015_ = lean_array_get_size(v_vs_2013_);
v___x_2016_ = lean_nat_dec_lt(v___x_2014_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_dec(v___x_2014_);
return v_x_1993_;
}
else
{
size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_usize_of_nat(v___x_2014_);
lean_dec(v___x_2014_);
v___x_2018_ = lean_usize_of_nat(v___x_2015_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2013_, v___x_2017_, v___x_2018_, v_x_1993_);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
size_t v_x_1125__boxed_2024_; size_t v_x_1126__boxed_2025_; lean_object* v_res_2026_; 
v_x_1125__boxed_2024_ = lean_unbox_usize(v_x_2021_);
lean_dec(v_x_2021_);
v_x_1126__boxed_2025_ = lean_unbox_usize(v_x_2022_);
lean_dec(v_x_2022_);
v_res_2026_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2020_, v_x_1125__boxed_2024_, v_x_1126__boxed_2025_, v_x_2023_);
lean_dec_ref(v_x_2020_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2027_, lean_object* v_init_2028_, lean_object* v_start_2029_){
_start:
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = lean_unsigned_to_nat(0u);
v___x_2031_ = lean_nat_dec_eq(v_start_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v_root_2032_; lean_object* v_tail_2033_; size_t v_shift_2034_; lean_object* v_tailOff_2035_; uint8_t v___x_2036_; 
v_root_2032_ = lean_ctor_get(v_t_2027_, 0);
v_tail_2033_ = lean_ctor_get(v_t_2027_, 1);
v_shift_2034_ = lean_ctor_get_usize(v_t_2027_, 4);
v_tailOff_2035_ = lean_ctor_get(v_t_2027_, 3);
v___x_2036_ = lean_nat_dec_le(v_tailOff_2035_, v_start_2029_);
if (v___x_2036_ == 0)
{
size_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2037_ = lean_usize_of_nat(v_start_2029_);
v___x_2038_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2032_, v___x_2037_, v_shift_2034_, v_init_2028_);
v___x_2039_ = lean_array_get_size(v_tail_2033_);
v___x_2040_ = lean_nat_dec_lt(v___x_2030_, v___x_2039_);
if (v___x_2040_ == 0)
{
return v___x_2038_;
}
else
{
size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = ((size_t)0ULL);
v___x_2042_ = lean_usize_of_nat(v___x_2039_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2033_, v___x_2041_, v___x_2042_, v___x_2038_);
return v___x_2043_;
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_nat_sub(v_start_2029_, v_tailOff_2035_);
v___x_2045_ = lean_array_get_size(v_tail_2033_);
v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_dec(v___x_2044_);
return v_init_2028_;
}
else
{
size_t v___x_2047_; size_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_usize_of_nat(v___x_2044_);
lean_dec(v___x_2044_);
v___x_2048_ = lean_usize_of_nat(v___x_2045_);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2033_, v___x_2047_, v___x_2048_, v_init_2028_);
return v___x_2049_;
}
}
}
else
{
lean_object* v_root_2050_; lean_object* v_tail_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v_root_2050_ = lean_ctor_get(v_t_2027_, 0);
v_tail_2051_ = lean_ctor_get(v_t_2027_, 1);
v___x_2052_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2050_, v_init_2028_);
v___x_2053_ = lean_array_get_size(v_tail_2051_);
v___x_2054_ = lean_nat_dec_lt(v___x_2030_, v___x_2053_);
if (v___x_2054_ == 0)
{
return v___x_2052_;
}
else
{
size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((size_t)0ULL);
v___x_2056_ = lean_usize_of_nat(v___x_2053_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2051_, v___x_2055_, v___x_2056_, v___x_2052_);
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2058_, lean_object* v_init_2059_, lean_object* v_start_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2058_, v_init_2059_, v_start_2060_);
lean_dec(v_start_2060_);
lean_dec_ref(v_t_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2062_, lean_object* v_t_u2082_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2062_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2063_, v_t_u2081_2062_, v___x_2065_);
return v___x_2066_;
}
else
{
lean_dec_ref(v_t_u2081_2062_);
lean_inc_ref(v_t_u2082_2063_);
return v_t_u2082_2063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2067_, lean_object* v_t_u2082_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2067_, v_t_u2082_2068_);
lean_dec_ref(v_t_u2082_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2070_, lean_object* v_t_u2081_2071_, lean_object* v_t_u2082_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2071_, v_t_u2082_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_t_u2081_2075_, lean_object* v_t_u2082_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_PersistentArray_append(v_00_u03b1_2074_, v_t_u2081_2075_, v_t_u2082_2076_);
lean_dec_ref(v_t_u2082_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2078_, lean_object* v_t_2079_, lean_object* v_init_2080_, lean_object* v_start_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2079_, v_init_2080_, v_start_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2083_, lean_object* v_t_2084_, lean_object* v_init_2085_, lean_object* v_start_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2083_, v_t_2084_, v_init_2085_, v_start_2086_);
lean_dec(v_start_2086_);
lean_dec_ref(v_t_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2088_, lean_object* v_x_2089_, size_t v_x_2090_, size_t v_x_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2089_, v_x_2090_, v_x_2091_, v_x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
size_t v_x_1241__boxed_2099_; size_t v_x_1242__boxed_2100_; lean_object* v_res_2101_; 
v_x_1241__boxed_2099_ = lean_unbox_usize(v_x_2096_);
lean_dec(v_x_2096_);
v_x_1242__boxed_2100_ = lean_unbox_usize(v_x_2097_);
lean_dec(v_x_2097_);
v_res_2101_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2094_, v_x_2095_, v_x_1241__boxed_2099_, v_x_1242__boxed_2100_, v_x_2098_);
lean_dec_ref(v_x_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2102_, lean_object* v_as_2103_, size_t v_i_2104_, size_t v_stop_2105_, lean_object* v_b_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2103_, v_i_2104_, v_stop_2105_, v_b_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_as_2109_, lean_object* v_i_2110_, lean_object* v_stop_2111_, lean_object* v_b_2112_){
_start:
{
size_t v_i_boxed_2113_; size_t v_stop_boxed_2114_; lean_object* v_res_2115_; 
v_i_boxed_2113_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_stop_boxed_2114_ = lean_unbox_usize(v_stop_2111_);
lean_dec(v_stop_2111_);
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2108_, v_as_2109_, v_i_boxed_2113_, v_stop_boxed_2114_, v_b_2112_);
lean_dec_ref(v_as_2109_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2116_, lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2117_, v_x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2120_, v_x_2121_, v_x_2122_);
lean_dec_ref(v_x_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2124_, lean_object* v_as_2125_, size_t v_i_2126_, size_t v_stop_2127_, lean_object* v_b_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2125_, v_i_2126_, v_stop_2127_, v_b_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_as_2131_, lean_object* v_i_2132_, lean_object* v_stop_2133_, lean_object* v_b_2134_){
_start:
{
size_t v_i_boxed_2135_; size_t v_stop_boxed_2136_; lean_object* v_res_2137_; 
v_i_boxed_2135_ = lean_unbox_usize(v_i_2132_);
lean_dec(v_i_2132_);
v_stop_boxed_2136_ = lean_unbox_usize(v_stop_2133_);
lean_dec(v_stop_2133_);
v_res_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2130_, v_as_2131_, v_i_boxed_2135_, v_stop_boxed_2136_, v_b_2134_);
lean_dec_ref(v_as_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg(){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg___boxed(lean_object* v___dummy_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_PersistentArray_instAppend___redArg();
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_apply_1(v_f_2145_, v_x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2148_, lean_object* v_f_2149_){
_start:
{
lean_object* v___f_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___f_2150_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2150_, 0, v_f_2149_);
v___x_2151_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2152_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2151_, v_t_2148_, v___f_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_t_2155_, lean_object* v_f_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2157_, 0, v_f_2156_);
v___x_2158_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2159_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2158_, v_t_2155_, v___f_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2160_, lean_object* v_f_2161_){
_start:
{
lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___f_2162_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2162_, 0, v_f_2161_);
v___x_2163_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2164_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2163_, v_t_2160_, v___f_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_t_2167_, lean_object* v_f_2168_){
_start:
{
lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2169_, 0, v_f_2168_);
v___x_2170_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2171_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2170_, v_t_2167_, v___f_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2172_, size_t v_i_2173_, size_t v_stop_2174_, lean_object* v_b_2175_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_eq(v_i_2173_, v_stop_2174_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; 
v___x_2177_ = lean_array_uget_borrowed(v_as_2172_, v_i_2173_);
lean_inc(v___x_2177_);
v___x_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v_b_2175_);
v___x_2179_ = ((size_t)1ULL);
v___x_2180_ = lean_usize_add(v_i_2173_, v___x_2179_);
v_i_2173_ = v___x_2180_;
v_b_2175_ = v___x_2178_;
goto _start;
}
else
{
return v_b_2175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2182_, lean_object* v_i_2183_, lean_object* v_stop_2184_, lean_object* v_b_2185_){
_start:
{
size_t v_i_boxed_2186_; size_t v_stop_boxed_2187_; lean_object* v_res_2188_; 
v_i_boxed_2186_ = lean_unbox_usize(v_i_2183_);
lean_dec(v_i_2183_);
v_stop_boxed_2187_ = lean_unbox_usize(v_stop_2184_);
lean_dec(v_stop_2184_);
v_res_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2182_, v_i_boxed_2186_, v_stop_boxed_2187_, v_b_2185_);
lean_dec_ref(v_as_2182_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
lean_object* v_cs_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v_cs_2191_ = lean_ctor_get(v_x_2189_, 0);
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_array_get_size(v_cs_2191_);
v___x_2194_ = lean_nat_dec_lt(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
return v_x_2190_;
}
else
{
size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = lean_usize_of_nat(v___x_2193_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2191_, v___x_2195_, v___x_2196_, v_x_2190_);
return v___x_2197_;
}
}
else
{
lean_object* v_vs_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_vs_2198_ = lean_ctor_get(v_x_2189_, 0);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_array_get_size(v_vs_2198_);
v___x_2201_ = lean_nat_dec_lt(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
return v_x_2190_;
}
else
{
size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = lean_usize_of_nat(v___x_2200_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2198_, v___x_2202_, v___x_2203_, v_x_2190_);
return v___x_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2205_, size_t v_i_2206_, size_t v_stop_2207_, lean_object* v_b_2208_){
_start:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_usize_dec_eq(v_i_2206_, v_stop_2207_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; 
v___x_2210_ = lean_array_uget_borrowed(v_as_2205_, v_i_2206_);
v___x_2211_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2210_, v_b_2208_);
v___x_2212_ = ((size_t)1ULL);
v___x_2213_ = lean_usize_add(v_i_2206_, v___x_2212_);
v_i_2206_ = v___x_2213_;
v_b_2208_ = v___x_2211_;
goto _start;
}
else
{
return v_b_2208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2215_, lean_object* v_i_2216_, lean_object* v_stop_2217_, lean_object* v_b_2218_){
_start:
{
size_t v_i_boxed_2219_; size_t v_stop_boxed_2220_; lean_object* v_res_2221_; 
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_stop_boxed_2220_ = lean_unbox_usize(v_stop_2217_);
lean_dec(v_stop_2217_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2215_, v_i_boxed_2219_, v_stop_boxed_2220_, v_b_2218_);
lean_dec_ref(v_as_2215_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2222_, lean_object* v_x_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2222_, v_x_2223_);
lean_dec_ref(v_x_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2225_, size_t v_x_2226_, size_t v_x_2227_, lean_object* v_x_2228_){
_start:
{
if (lean_obj_tag(v_x_2225_) == 0)
{
lean_object* v_cs_2229_; lean_object* v___x_2230_; size_t v___x_2231_; lean_object* v_j_2232_; lean_object* v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; size_t v___x_2237_; size_t v___x_2238_; size_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_cs_2229_ = lean_ctor_get(v_x_2225_, 0);
v___x_2230_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2231_ = lean_usize_shift_right(v_x_2226_, v_x_2227_);
v_j_2232_ = lean_usize_to_nat(v___x_2231_);
v___x_2233_ = lean_array_get_borrowed(v___x_2230_, v_cs_2229_, v_j_2232_);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_shift_left(v___x_2234_, v_x_2227_);
v___x_2236_ = lean_usize_sub(v___x_2235_, v___x_2234_);
v___x_2237_ = lean_usize_land(v_x_2226_, v___x_2236_);
v___x_2238_ = ((size_t)5ULL);
v___x_2239_ = lean_usize_sub(v_x_2227_, v___x_2238_);
v___x_2240_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2233_, v___x_2237_, v___x_2239_, v_x_2228_);
v___x_2241_ = lean_unsigned_to_nat(1u);
v___x_2242_ = lean_nat_add(v_j_2232_, v___x_2241_);
lean_dec(v_j_2232_);
v___x_2243_ = lean_array_get_size(v_cs_2229_);
v___x_2244_ = lean_nat_dec_lt(v___x_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec(v___x_2242_);
return v___x_2240_;
}
else
{
size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_usize_of_nat(v___x_2242_);
lean_dec(v___x_2242_);
v___x_2246_ = lean_usize_of_nat(v___x_2243_);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2229_, v___x_2245_, v___x_2246_, v___x_2240_);
return v___x_2247_;
}
}
else
{
lean_object* v_vs_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_vs_2248_ = lean_ctor_get(v_x_2225_, 0);
v___x_2249_ = lean_usize_to_nat(v_x_2226_);
v___x_2250_ = lean_array_get_size(v_vs_2248_);
v___x_2251_ = lean_nat_dec_lt(v___x_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_dec(v___x_2249_);
return v_x_2228_;
}
else
{
size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_usize_of_nat(v___x_2249_);
lean_dec(v___x_2249_);
v___x_2253_ = lean_usize_of_nat(v___x_2250_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2248_, v___x_2252_, v___x_2253_, v_x_2228_);
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
size_t v_x_1119__boxed_2259_; size_t v_x_1120__boxed_2260_; lean_object* v_res_2261_; 
v_x_1119__boxed_2259_ = lean_unbox_usize(v_x_2256_);
lean_dec(v_x_2256_);
v_x_1120__boxed_2260_ = lean_unbox_usize(v_x_2257_);
lean_dec(v_x_2257_);
v_res_2261_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2255_, v_x_1119__boxed_2259_, v_x_1120__boxed_2260_, v_x_2258_);
lean_dec_ref(v_x_2255_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2262_, lean_object* v_init_2263_, lean_object* v_start_2264_){
_start:
{
lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_nat_dec_eq(v_start_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v_root_2267_; lean_object* v_tail_2268_; size_t v_shift_2269_; lean_object* v_tailOff_2270_; uint8_t v___x_2271_; 
v_root_2267_ = lean_ctor_get(v_t_2262_, 0);
v_tail_2268_ = lean_ctor_get(v_t_2262_, 1);
v_shift_2269_ = lean_ctor_get_usize(v_t_2262_, 4);
v_tailOff_2270_ = lean_ctor_get(v_t_2262_, 3);
v___x_2271_ = lean_nat_dec_le(v_tailOff_2270_, v_start_2264_);
if (v___x_2271_ == 0)
{
size_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2272_ = lean_usize_of_nat(v_start_2264_);
v___x_2273_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2267_, v___x_2272_, v_shift_2269_, v_init_2263_);
v___x_2274_ = lean_array_get_size(v_tail_2268_);
v___x_2275_ = lean_nat_dec_lt(v___x_2265_, v___x_2274_);
if (v___x_2275_ == 0)
{
return v___x_2273_;
}
else
{
size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = lean_usize_of_nat(v___x_2274_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2268_, v___x_2276_, v___x_2277_, v___x_2273_);
return v___x_2278_;
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2279_ = lean_nat_sub(v_start_2264_, v_tailOff_2270_);
v___x_2280_ = lean_array_get_size(v_tail_2268_);
v___x_2281_ = lean_nat_dec_lt(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_dec(v___x_2279_);
return v_init_2263_;
}
else
{
size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_usize_of_nat(v___x_2279_);
lean_dec(v___x_2279_);
v___x_2283_ = lean_usize_of_nat(v___x_2280_);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2268_, v___x_2282_, v___x_2283_, v_init_2263_);
return v___x_2284_;
}
}
}
else
{
lean_object* v_root_2285_; lean_object* v_tail_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_root_2285_ = lean_ctor_get(v_t_2262_, 0);
v_tail_2286_ = lean_ctor_get(v_t_2262_, 1);
v___x_2287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2285_, v_init_2263_);
v___x_2288_ = lean_array_get_size(v_tail_2286_);
v___x_2289_ = lean_nat_dec_lt(v___x_2265_, v___x_2288_);
if (v___x_2289_ == 0)
{
return v___x_2287_;
}
else
{
size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = lean_usize_of_nat(v___x_2288_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2286_, v___x_2290_, v___x_2291_, v___x_2287_);
return v___x_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2293_, lean_object* v_init_2294_, lean_object* v_start_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2293_, v_init_2294_, v_start_2295_);
lean_dec(v_start_2295_);
lean_dec_ref(v_t_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2297_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2297_, v___x_2298_, v___x_2299_);
v___x_2301_ = l_List_reverse___redArg(v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_PersistentArray_toList___redArg(v_t_2302_);
lean_dec_ref(v_t_2302_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2304_, lean_object* v_t_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_PersistentArray_toList___redArg(v_t_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_t_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_PersistentArray_toList(v_00_u03b1_2307_, v_t_2308_);
lean_dec_ref(v_t_2308_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2310_, lean_object* v_t_2311_, lean_object* v_init_2312_, lean_object* v_start_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2311_, v_init_2312_, v_start_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2315_, lean_object* v_t_2316_, lean_object* v_init_2317_, lean_object* v_start_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2315_, v_t_2316_, v_init_2317_, v_start_2318_);
lean_dec(v_start_2318_);
lean_dec_ref(v_t_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2320_, lean_object* v_x_2321_, size_t v_x_2322_, size_t v_x_2323_, lean_object* v_x_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2321_, v_x_2322_, v_x_2323_, v_x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
size_t v_x_1237__boxed_2331_; size_t v_x_1238__boxed_2332_; lean_object* v_res_2333_; 
v_x_1237__boxed_2331_ = lean_unbox_usize(v_x_2328_);
lean_dec(v_x_2328_);
v_x_1238__boxed_2332_ = lean_unbox_usize(v_x_2329_);
lean_dec(v_x_2329_);
v_res_2333_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2326_, v_x_2327_, v_x_1237__boxed_2331_, v_x_1238__boxed_2332_, v_x_2330_);
lean_dec_ref(v_x_2327_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2334_, lean_object* v_as_2335_, size_t v_i_2336_, size_t v_stop_2337_, lean_object* v_b_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2335_, v_i_2336_, v_stop_2337_, v_b_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_as_2341_, lean_object* v_i_2342_, lean_object* v_stop_2343_, lean_object* v_b_2344_){
_start:
{
size_t v_i_boxed_2345_; size_t v_stop_boxed_2346_; lean_object* v_res_2347_; 
v_i_boxed_2345_ = lean_unbox_usize(v_i_2342_);
lean_dec(v_i_2342_);
v_stop_boxed_2346_ = lean_unbox_usize(v_stop_2343_);
lean_dec(v_stop_2343_);
v_res_2347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2340_, v_as_2341_, v_i_boxed_2345_, v_stop_boxed_2346_, v_b_2344_);
lean_dec_ref(v_as_2341_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2349_, v_x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2352_, v_x_2353_, v_x_2354_);
lean_dec_ref(v_x_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2356_, lean_object* v_as_2357_, size_t v_i_2358_, size_t v_stop_2359_, lean_object* v_b_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2357_, v_i_2358_, v_stop_2359_, v_b_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2362_, lean_object* v_as_2363_, lean_object* v_i_2364_, lean_object* v_stop_2365_, lean_object* v_b_2366_){
_start:
{
size_t v_i_boxed_2367_; size_t v_stop_boxed_2368_; lean_object* v_res_2369_; 
v_i_boxed_2367_ = lean_unbox_usize(v_i_2364_);
lean_dec(v_i_2364_);
v_stop_boxed_2368_ = lean_unbox_usize(v_stop_2365_);
lean_dec(v_stop_2365_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2362_, v_as_2363_, v_i_boxed_2367_, v_stop_boxed_2368_, v_b_2366_);
lean_dec_ref(v_as_2363_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2370_, lean_object* v_p_2371_, lean_object* v_x_2372_){
_start:
{
if (lean_obj_tag(v_x_2372_) == 0)
{
lean_object* v_toApplicative_2373_; lean_object* v_cs_2374_; lean_object* v_toPure_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_toApplicative_2373_ = lean_ctor_get(v_inst_2370_, 0);
v_cs_2374_ = lean_ctor_get(v_x_2372_, 0);
lean_inc_ref(v_cs_2374_);
lean_dec_ref_known(v_x_2372_, 1);
v_toPure_2375_ = lean_ctor_get(v_toApplicative_2373_, 1);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = lean_array_get_size(v_cs_2374_);
v___x_2378_ = lean_nat_dec_lt(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_inc(v_toPure_2375_);
lean_dec_ref(v_cs_2374_);
lean_dec(v_p_2371_);
lean_dec_ref(v_inst_2370_);
v___x_2379_ = lean_box(v___x_2378_);
v___x_2380_ = lean_apply_2(v_toPure_2375_, lean_box(0), v___x_2379_);
return v___x_2380_;
}
else
{
if (v___x_2378_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_inc(v_toPure_2375_);
lean_dec_ref(v_cs_2374_);
lean_dec(v_p_2371_);
lean_dec_ref(v_inst_2370_);
v___x_2381_ = lean_box(v___x_2378_);
v___x_2382_ = lean_apply_2(v_toPure_2375_, lean_box(0), v___x_2381_);
return v___x_2382_;
}
else
{
lean_object* v___f_2383_; size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
lean_inc_ref(v_inst_2370_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2383_, 0, v_inst_2370_);
lean_closure_set(v___f_2383_, 1, v_p_2371_);
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = lean_usize_of_nat(v___x_2377_);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2370_, v___f_2383_, v_cs_2374_, v___x_2384_, v___x_2385_);
return v___x_2386_;
}
}
}
else
{
lean_object* v_toApplicative_2387_; lean_object* v_vs_2388_; lean_object* v_toPure_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_toApplicative_2387_ = lean_ctor_get(v_inst_2370_, 0);
v_vs_2388_ = lean_ctor_get(v_x_2372_, 0);
lean_inc_ref(v_vs_2388_);
lean_dec_ref_known(v_x_2372_, 1);
v_toPure_2389_ = lean_ctor_get(v_toApplicative_2387_, 1);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = lean_array_get_size(v_vs_2388_);
v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_inc(v_toPure_2389_);
lean_dec_ref(v_vs_2388_);
lean_dec(v_p_2371_);
lean_dec_ref(v_inst_2370_);
v___x_2393_ = lean_box(v___x_2392_);
v___x_2394_ = lean_apply_2(v_toPure_2389_, lean_box(0), v___x_2393_);
return v___x_2394_;
}
else
{
if (v___x_2392_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_inc(v_toPure_2389_);
lean_dec_ref(v_vs_2388_);
lean_dec(v_p_2371_);
lean_dec_ref(v_inst_2370_);
v___x_2395_ = lean_box(v___x_2392_);
v___x_2396_ = lean_apply_2(v_toPure_2389_, lean_box(0), v___x_2395_);
return v___x_2396_;
}
else
{
size_t v___x_2397_; size_t v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = ((size_t)0ULL);
v___x_2398_ = lean_usize_of_nat(v___x_2391_);
v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2370_, v_p_2371_, v_vs_2388_, v___x_2397_, v___x_2398_);
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2400_, lean_object* v_p_2401_, lean_object* v_c_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2400_, v_p_2401_, v_c_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2404_, lean_object* v_m_2405_, lean_object* v_inst_2406_, lean_object* v_p_2407_, lean_object* v_x_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2406_, v_p_2407_, v_x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2410_, lean_object* v_toPure_2411_, lean_object* v_inst_2412_, lean_object* v_p_2413_, uint8_t v_b_2414_){
_start:
{
if (v_b_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = lean_array_get_size(v_tail_2410_);
v___x_2417_ = lean_nat_dec_lt(v___x_2415_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_p_2413_);
lean_dec_ref(v_inst_2412_);
lean_dec_ref(v_tail_2410_);
v___x_2418_ = lean_box(v___x_2417_);
v___x_2419_ = lean_apply_2(v_toPure_2411_, lean_box(0), v___x_2418_);
return v___x_2419_;
}
else
{
if (v___x_2417_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec(v_p_2413_);
lean_dec_ref(v_inst_2412_);
lean_dec_ref(v_tail_2410_);
v___x_2420_ = lean_box(v___x_2417_);
v___x_2421_ = lean_apply_2(v_toPure_2411_, lean_box(0), v___x_2420_);
return v___x_2421_;
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v_toPure_2411_);
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2416_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2412_, v_p_2413_, v_tail_2410_, v___x_2422_, v___x_2423_);
return v___x_2424_;
}
}
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v_p_2413_);
lean_dec_ref(v_inst_2412_);
lean_dec_ref(v_tail_2410_);
v___x_2425_ = lean_box(v_b_2414_);
v___x_2426_ = lean_apply_2(v_toPure_2411_, lean_box(0), v___x_2425_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2427_, lean_object* v_toPure_2428_, lean_object* v_inst_2429_, lean_object* v_p_2430_, lean_object* v_b_2431_){
_start:
{
uint8_t v_b_boxed_2432_; lean_object* v_res_2433_; 
v_b_boxed_2432_ = lean_unbox(v_b_2431_);
v_res_2433_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2427_, v_toPure_2428_, v_inst_2429_, v_p_2430_, v_b_boxed_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2434_, lean_object* v_t_2435_, lean_object* v_p_2436_){
_start:
{
lean_object* v_toApplicative_2437_; lean_object* v_toBind_2438_; lean_object* v_root_2439_; lean_object* v_tail_2440_; lean_object* v_toPure_2441_; lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; 
v_toApplicative_2437_ = lean_ctor_get(v_inst_2434_, 0);
v_toBind_2438_ = lean_ctor_get(v_inst_2434_, 1);
lean_inc(v_toBind_2438_);
v_root_2439_ = lean_ctor_get(v_t_2435_, 0);
lean_inc_ref(v_root_2439_);
v_tail_2440_ = lean_ctor_get(v_t_2435_, 1);
lean_inc_ref(v_tail_2440_);
lean_dec_ref(v_t_2435_);
v_toPure_2441_ = lean_ctor_get(v_toApplicative_2437_, 1);
lean_inc(v_toPure_2441_);
lean_inc(v_p_2436_);
lean_inc_ref(v_inst_2434_);
v___x_2442_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2434_, v_p_2436_, v_root_2439_);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2443_, 0, v_tail_2440_);
lean_closure_set(v___f_2443_, 1, v_toPure_2441_);
lean_closure_set(v___f_2443_, 2, v_inst_2434_);
lean_closure_set(v___f_2443_, 3, v_p_2436_);
v___x_2444_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v___x_2442_, v___f_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2445_, lean_object* v_m_2446_, lean_object* v_inst_2447_, lean_object* v_t_2448_, lean_object* v_p_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2447_, v_t_2448_, v_p_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2451_, uint8_t v_b_2452_){
_start:
{
if (v_b_2452_ == 0)
{
uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = 1;
v___x_2454_ = lean_box(v___x_2453_);
v___x_2455_ = lean_apply_2(v_toPure_2451_, lean_box(0), v___x_2454_);
return v___x_2455_;
}
else
{
uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = 0;
v___x_2457_ = lean_box(v___x_2456_);
v___x_2458_ = lean_apply_2(v_toPure_2451_, lean_box(0), v___x_2457_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2459_, lean_object* v_b_2460_){
_start:
{
uint8_t v_b_boxed_2461_; lean_object* v_res_2462_; 
v_b_boxed_2461_ = lean_unbox(v_b_2460_);
v_res_2462_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2459_, v_b_boxed_2461_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2463_, lean_object* v_toBind_2464_, lean_object* v___f_2465_, lean_object* v_v_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_apply_1(v_p_2463_, v_v_2466_);
v___x_2468_ = lean_apply_4(v_toBind_2464_, lean_box(0), lean_box(0), v___x_2467_, v___f_2465_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2469_, lean_object* v_a_2470_, lean_object* v_p_2471_){
_start:
{
lean_object* v_toApplicative_2472_; lean_object* v_toBind_2473_; lean_object* v_toPure_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_toApplicative_2472_ = lean_ctor_get(v_inst_2469_, 0);
v_toBind_2473_ = lean_ctor_get(v_inst_2469_, 1);
lean_inc_n(v_toBind_2473_, 2);
v_toPure_2474_ = lean_ctor_get(v_toApplicative_2472_, 1);
lean_inc(v_toPure_2474_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2475_, 0, v_toPure_2474_);
lean_inc_ref(v___f_2475_);
v___f_2476_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2476_, 0, v_p_2471_);
lean_closure_set(v___f_2476_, 1, v_toBind_2473_);
lean_closure_set(v___f_2476_, 2, v___f_2475_);
v___x_2477_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2469_, v_a_2470_, v___f_2476_);
v___x_2478_ = lean_apply_4(v_toBind_2473_, lean_box(0), lean_box(0), v___x_2477_, v___f_2475_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2479_, lean_object* v_m_2480_, lean_object* v_inst_2481_, lean_object* v_a_2482_, lean_object* v_p_2483_){
_start:
{
lean_object* v_toApplicative_2484_; lean_object* v_toBind_2485_; lean_object* v_toPure_2486_; lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_toApplicative_2484_ = lean_ctor_get(v_inst_2481_, 0);
v_toBind_2485_ = lean_ctor_get(v_inst_2481_, 1);
lean_inc_n(v_toBind_2485_, 2);
v_toPure_2486_ = lean_ctor_get(v_toApplicative_2484_, 1);
lean_inc(v_toPure_2486_);
v___f_2487_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2487_, 0, v_toPure_2486_);
lean_inc_ref(v___f_2487_);
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2488_, 0, v_p_2483_);
lean_closure_set(v___f_2488_, 1, v_toBind_2485_);
lean_closure_set(v___f_2488_, 2, v___f_2487_);
v___x_2489_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2481_, v_a_2482_, v___f_2488_);
v___x_2490_ = lean_apply_4(v_toBind_2485_, lean_box(0), lean_box(0), v___x_2489_, v___f_2487_);
return v___x_2490_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2491_, lean_object* v_x_2492_){
_start:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = lean_apply_1(v_p_2491_, v_x_2492_);
v___x_2494_ = lean_unbox(v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2495_, lean_object* v_x_2496_){
_start:
{
uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_res_2497_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2495_, v_x_2496_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg(lean_object* v_a_2499_, lean_object* v_p_2500_){
_start:
{
lean_object* v___f_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___f_2501_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2501_, 0, v_p_2500_);
v___x_2502_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2503_ = l_Lean_PersistentArray_anyM___redArg(v___x_2502_, v_a_2499_, v___f_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2504_, lean_object* v_a_2505_, lean_object* v_p_2506_){
_start:
{
lean_object* v___f_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2507_, 0, v_p_2506_);
v___x_2508_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2509_ = l_Lean_PersistentArray_anyM___redArg(v___x_2508_, v_a_2505_, v___f_2507_);
v___x_2510_ = lean_unbox(v___x_2509_);
lean_dec(v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2511_, lean_object* v_a_2512_, lean_object* v_p_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_Lean_PersistentArray_any(v_00_u03b1_2511_, v_a_2512_, v_p_2513_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2516_, lean_object* v_x_2517_){
_start:
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = lean_apply_1(v_p_2516_, v_x_2517_);
v___x_2519_ = lean_unbox(v___x_2518_);
if (v___x_2519_ == 0)
{
uint8_t v___x_2520_; 
v___x_2520_ = 1;
return v___x_2520_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = 0;
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2522_, lean_object* v_x_2523_){
_start:
{
uint8_t v_res_2524_; lean_object* v_r_2525_; 
v_res_2524_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2522_, v_x_2523_);
v_r_2525_ = lean_box(v_res_2524_);
return v_r_2525_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2526_, lean_object* v_p_2527_){
_start:
{
lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___f_2528_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2528_, 0, v_p_2527_);
v___x_2529_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2530_ = l_Lean_PersistentArray_anyM___redArg(v___x_2529_, v_a_2526_, v___f_2528_);
v___x_2531_ = lean_unbox(v___x_2530_);
lean_dec(v___x_2530_);
if (v___x_2531_ == 0)
{
uint8_t v___x_2532_; 
v___x_2532_ = 1;
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; 
v___x_2533_ = 0;
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2534_, lean_object* v_p_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_Lean_PersistentArray_all___redArg(v_a_2534_, v_p_2535_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2538_, lean_object* v_a_2539_, lean_object* v_p_2540_){
_start:
{
lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___f_2541_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2541_, 0, v_p_2540_);
v___x_2542_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2543_ = l_Lean_PersistentArray_anyM___redArg(v___x_2542_, v_a_2539_, v___f_2541_);
v___x_2544_ = lean_unbox(v___x_2543_);
lean_dec(v___x_2543_);
if (v___x_2544_ == 0)
{
uint8_t v___x_2545_; 
v___x_2545_ = 1;
return v___x_2545_;
}
else
{
uint8_t v___x_2546_; 
v___x_2546_ = 0;
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2547_, lean_object* v_a_2548_, lean_object* v_p_2549_){
_start:
{
uint8_t v_res_2550_; lean_object* v_r_2551_; 
v_res_2550_ = l_Lean_PersistentArray_all(v_00_u03b1_2547_, v_a_2548_, v_p_2549_);
v_r_2551_ = lean_box(v_res_2550_);
return v_r_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_cs_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_vs_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2558_, lean_object* v_f_2559_, lean_object* v_x_2560_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v_toApplicative_2561_; lean_object* v_toFunctor_2562_; lean_object* v_cs_2563_; lean_object* v_map_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; size_t v_sz_2567_; size_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_toApplicative_2561_ = lean_ctor_get(v_inst_2558_, 0);
v_toFunctor_2562_ = lean_ctor_get(v_toApplicative_2561_, 0);
v_cs_2563_ = lean_ctor_get(v_x_2560_, 0);
lean_inc_ref(v_cs_2563_);
lean_dec_ref_known(v_x_2560_, 1);
v_map_2564_ = lean_ctor_get(v_toFunctor_2562_, 0);
lean_inc(v_map_2564_);
v___f_2565_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2558_);
v___f_2566_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2566_, 0, v_inst_2558_);
lean_closure_set(v___f_2566_, 1, v_f_2559_);
v_sz_2567_ = lean_array_size(v_cs_2563_);
v___x_2568_ = ((size_t)0ULL);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2558_, v___f_2566_, v_sz_2567_, v___x_2568_, v_cs_2563_);
v___x_2570_ = lean_apply_4(v_map_2564_, lean_box(0), lean_box(0), v___f_2565_, v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v_toApplicative_2571_; lean_object* v_toFunctor_2572_; lean_object* v_vs_2573_; lean_object* v_map_2574_; lean_object* v___f_2575_; size_t v_sz_2576_; size_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_toApplicative_2571_ = lean_ctor_get(v_inst_2558_, 0);
v_toFunctor_2572_ = lean_ctor_get(v_toApplicative_2571_, 0);
v_vs_2573_ = lean_ctor_get(v_x_2560_, 0);
lean_inc_ref(v_vs_2573_);
lean_dec_ref_known(v_x_2560_, 1);
v_map_2574_ = lean_ctor_get(v_toFunctor_2572_, 0);
lean_inc(v_map_2574_);
v___f_2575_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2576_ = lean_array_size(v_vs_2573_);
v___x_2577_ = ((size_t)0ULL);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2558_, v_f_2559_, v_sz_2576_, v___x_2577_, v_vs_2573_);
v___x_2579_ = lean_apply_4(v_map_2574_, lean_box(0), lean_box(0), v___f_2575_, v___x_2578_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2580_, lean_object* v_f_2581_, lean_object* v_c_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2580_, v_f_2581_, v_c_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2584_, lean_object* v_m_2585_, lean_object* v_inst_2586_, lean_object* v_00_u03b2_2587_, lean_object* v_f_2588_, lean_object* v_x_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2586_, v_f_2588_, v_x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2591_, lean_object* v_size_2592_, size_t v_shift_2593_, lean_object* v_tailOff_2594_, lean_object* v_toPure_2595_, lean_object* v_tail_2596_){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2597_, 0, v_root_2591_);
lean_ctor_set(v___x_2597_, 1, v_tail_2596_);
lean_ctor_set(v___x_2597_, 2, v_size_2592_);
lean_ctor_set(v___x_2597_, 3, v_tailOff_2594_);
lean_ctor_set_usize(v___x_2597_, 4, v_shift_2593_);
v___x_2598_ = lean_apply_2(v_toPure_2595_, lean_box(0), v___x_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2599_, lean_object* v_size_2600_, lean_object* v_shift_2601_, lean_object* v_tailOff_2602_, lean_object* v_toPure_2603_, lean_object* v_tail_2604_){
_start:
{
size_t v_shift_boxed_2605_; lean_object* v_res_2606_; 
v_shift_boxed_2605_ = lean_unbox_usize(v_shift_2601_);
lean_dec(v_shift_2601_);
v_res_2606_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2599_, v_size_2600_, v_shift_boxed_2605_, v_tailOff_2602_, v_toPure_2603_, v_tail_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2607_, size_t v_shift_2608_, lean_object* v_tailOff_2609_, lean_object* v_toPure_2610_, lean_object* v_tail_2611_, lean_object* v_inst_2612_, lean_object* v_f_2613_, lean_object* v_toBind_2614_, lean_object* v_root_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___f_2617_; size_t v_sz_2618_; size_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2616_ = lean_box_usize(v_shift_2608_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2617_, 0, v_root_2615_);
lean_closure_set(v___f_2617_, 1, v_size_2607_);
lean_closure_set(v___f_2617_, 2, v___x_2616_);
lean_closure_set(v___f_2617_, 3, v_tailOff_2609_);
lean_closure_set(v___f_2617_, 4, v_toPure_2610_);
v_sz_2618_ = lean_array_size(v_tail_2611_);
v___x_2619_ = ((size_t)0ULL);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2612_, v_f_2613_, v_sz_2618_, v___x_2619_, v_tail_2611_);
v___x_2621_ = lean_apply_4(v_toBind_2614_, lean_box(0), lean_box(0), v___x_2620_, v___f_2617_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2622_, lean_object* v_shift_2623_, lean_object* v_tailOff_2624_, lean_object* v_toPure_2625_, lean_object* v_tail_2626_, lean_object* v_inst_2627_, lean_object* v_f_2628_, lean_object* v_toBind_2629_, lean_object* v_root_2630_){
_start:
{
size_t v_shift_boxed_2631_; lean_object* v_res_2632_; 
v_shift_boxed_2631_ = lean_unbox_usize(v_shift_2623_);
lean_dec(v_shift_2623_);
v_res_2632_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2622_, v_shift_boxed_2631_, v_tailOff_2624_, v_toPure_2625_, v_tail_2626_, v_inst_2627_, v_f_2628_, v_toBind_2629_, v_root_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2633_, lean_object* v_f_2634_, lean_object* v_t_2635_){
_start:
{
lean_object* v_toApplicative_2636_; lean_object* v_toBind_2637_; lean_object* v_root_2638_; lean_object* v_tail_2639_; lean_object* v_size_2640_; size_t v_shift_2641_; lean_object* v_tailOff_2642_; lean_object* v_toPure_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; 
v_toApplicative_2636_ = lean_ctor_get(v_inst_2633_, 0);
v_toBind_2637_ = lean_ctor_get(v_inst_2633_, 1);
lean_inc_n(v_toBind_2637_, 2);
v_root_2638_ = lean_ctor_get(v_t_2635_, 0);
lean_inc_ref(v_root_2638_);
v_tail_2639_ = lean_ctor_get(v_t_2635_, 1);
lean_inc_ref(v_tail_2639_);
v_size_2640_ = lean_ctor_get(v_t_2635_, 2);
lean_inc(v_size_2640_);
v_shift_2641_ = lean_ctor_get_usize(v_t_2635_, 4);
v_tailOff_2642_ = lean_ctor_get(v_t_2635_, 3);
lean_inc(v_tailOff_2642_);
lean_dec_ref(v_t_2635_);
v_toPure_2643_ = lean_ctor_get(v_toApplicative_2636_, 1);
lean_inc(v_toPure_2643_);
lean_inc(v_f_2634_);
lean_inc_ref(v_inst_2633_);
v___x_2644_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2633_, v_f_2634_, v_root_2638_);
v___x_2645_ = lean_box_usize(v_shift_2641_);
v___f_2646_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2646_, 0, v_size_2640_);
lean_closure_set(v___f_2646_, 1, v___x_2645_);
lean_closure_set(v___f_2646_, 2, v_tailOff_2642_);
lean_closure_set(v___f_2646_, 3, v_toPure_2643_);
lean_closure_set(v___f_2646_, 4, v_tail_2639_);
lean_closure_set(v___f_2646_, 5, v_inst_2633_);
lean_closure_set(v___f_2646_, 6, v_f_2634_);
lean_closure_set(v___f_2646_, 7, v_toBind_2637_);
v___x_2647_ = lean_apply_4(v_toBind_2637_, lean_box(0), lean_box(0), v___x_2644_, v___f_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2648_, lean_object* v_m_2649_, lean_object* v_inst_2650_, lean_object* v_00_u03b2_2651_, lean_object* v_f_2652_, lean_object* v_t_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2650_, v_f_2652_, v_t_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_apply_1(v_f_2655_, v_x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2658_, lean_object* v_t_2659_){
_start:
{
lean_object* v___f_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2660_, 0, v_f_2658_);
v___x_2661_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2662_ = l_Lean_PersistentArray_mapM___redArg(v___x_2661_, v___f_2660_, v_t_2659_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2663_, lean_object* v_00_u03b2_2664_, lean_object* v_f_2665_, lean_object* v_t_2666_){
_start:
{
lean_object* v___f_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2667_, 0, v_f_2665_);
v___x_2668_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2669_ = l_Lean_PersistentArray_mapM___redArg(v___x_2668_, v___f_2667_, v_t_2666_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_){
_start:
{
if (lean_obj_tag(v_x_2670_) == 0)
{
lean_object* v_cs_2673_; lean_object* v_numNodes_2674_; lean_object* v_depth_2675_; lean_object* v_tailSize_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2694_; 
v_cs_2673_ = lean_ctor_get(v_x_2670_, 0);
v_numNodes_2674_ = lean_ctor_get(v_x_2671_, 0);
v_depth_2675_ = lean_ctor_get(v_x_2671_, 1);
v_tailSize_2676_ = lean_ctor_get(v_x_2671_, 2);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_x_2671_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2678_ = v_x_2671_;
v_isShared_2679_ = v_isSharedCheck_2694_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_tailSize_2676_);
lean_inc(v_depth_2675_);
lean_inc(v_numNodes_2674_);
lean_dec(v_x_2671_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2694_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___y_2683_; uint8_t v___x_2693_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_nat_add(v_numNodes_2674_, v___x_2680_);
lean_dec(v_numNodes_2674_);
v___x_2693_ = lean_nat_dec_le(v_x_2672_, v_depth_2675_);
if (v___x_2693_ == 0)
{
lean_dec(v_depth_2675_);
lean_inc(v_x_2672_);
v___y_2683_ = v_x_2672_;
goto v___jp_2682_;
}
else
{
v___y_2683_ = v_depth_2675_;
goto v___jp_2682_;
}
v___jp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___y_2683_);
lean_ctor_set(v___x_2678_, 0, v___x_2681_);
v___x_2685_ = v___x_2678_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___y_2683_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_tailSize_2676_);
v___x_2685_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_array_get_size(v_cs_2673_);
v___x_2688_ = lean_nat_dec_lt(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_dec(v_x_2672_);
return v___x_2685_;
}
else
{
size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((size_t)0ULL);
v___x_2690_ = lean_usize_of_nat(v___x_2687_);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2672_, v_cs_2673_, v___x_2689_, v___x_2690_, v___x_2685_);
lean_dec(v_x_2672_);
return v___x_2691_;
}
}
}
}
}
else
{
lean_object* v_numNodes_2695_; lean_object* v_depth_2696_; lean_object* v_tailSize_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2710_; 
v_numNodes_2695_ = lean_ctor_get(v_x_2671_, 0);
v_depth_2696_ = lean_ctor_get(v_x_2671_, 1);
v_tailSize_2697_ = lean_ctor_get(v_x_2671_, 2);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_x_2671_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2699_ = v_x_2671_;
v_isShared_2700_ = v_isSharedCheck_2710_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_tailSize_2697_);
lean_inc(v_depth_2696_);
lean_inc(v_numNodes_2695_);
lean_dec(v_x_2671_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2710_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_nat_add(v_numNodes_2695_, v___x_2701_);
lean_dec(v_numNodes_2695_);
v___x_2703_ = lean_nat_dec_le(v_x_2672_, v_depth_2696_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2705_; 
lean_dec(v_depth_2696_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v_x_2672_);
lean_ctor_set(v___x_2699_, 0, v___x_2702_);
v___x_2705_ = v___x_2699_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_x_2672_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_tailSize_2697_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
else
{
lean_object* v___x_2708_; 
lean_dec(v_x_2672_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2702_);
v___x_2708_ = v___x_2699_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_depth_2696_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_tailSize_2697_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2711_, lean_object* v_as_2712_, size_t v_i_2713_, size_t v_stop_2714_, lean_object* v_b_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = lean_usize_dec_eq(v_i_2713_, v_stop_2714_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; size_t v___x_2721_; size_t v___x_2722_; 
v___x_2717_ = lean_array_uget_borrowed(v_as_2712_, v_i_2713_);
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_nat_add(v_x_2711_, v___x_2718_);
v___x_2720_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2717_, v_b_2715_, v___x_2719_);
v___x_2721_ = ((size_t)1ULL);
v___x_2722_ = lean_usize_add(v_i_2713_, v___x_2721_);
v_i_2713_ = v___x_2722_;
v_b_2715_ = v___x_2720_;
goto _start;
}
else
{
return v_b_2715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2724_, lean_object* v_as_2725_, lean_object* v_i_2726_, lean_object* v_stop_2727_, lean_object* v_b_2728_){
_start:
{
size_t v_i_boxed_2729_; size_t v_stop_boxed_2730_; lean_object* v_res_2731_; 
v_i_boxed_2729_ = lean_unbox_usize(v_i_2726_);
lean_dec(v_i_2726_);
v_stop_boxed_2730_ = lean_unbox_usize(v_stop_2727_);
lean_dec(v_stop_2727_);
v_res_2731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2724_, v_as_2725_, v_i_boxed_2729_, v_stop_boxed_2730_, v_b_2728_);
lean_dec_ref(v_as_2725_);
lean_dec(v_x_2724_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2732_, lean_object* v_x_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2732_, v_x_2733_, v_x_2734_);
lean_dec_ref(v_x_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2737_, v_x_2738_, v_x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2741_, v_x_2742_, v_x_2743_, v_x_2744_);
lean_dec_ref(v_x_2742_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2746_, lean_object* v_x_2747_, lean_object* v_as_2748_, size_t v_i_2749_, size_t v_stop_2750_, lean_object* v_b_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2747_, v_as_2748_, v_i_2749_, v_stop_2750_, v_b_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_x_2754_, lean_object* v_as_2755_, lean_object* v_i_2756_, lean_object* v_stop_2757_, lean_object* v_b_2758_){
_start:
{
size_t v_i_boxed_2759_; size_t v_stop_boxed_2760_; lean_object* v_res_2761_; 
v_i_boxed_2759_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_stop_boxed_2760_ = lean_unbox_usize(v_stop_2757_);
lean_dec(v_stop_2757_);
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2753_, v_x_2754_, v_as_2755_, v_i_boxed_2759_, v_stop_boxed_2760_, v_b_2758_);
lean_dec_ref(v_as_2755_);
lean_dec(v_x_2754_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2762_){
_start:
{
lean_object* v_root_2763_; lean_object* v_tail_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_root_2763_ = lean_ctor_get(v_r_2762_, 0);
v_tail_2764_ = lean_ctor_get(v_r_2762_, 1);
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = lean_array_get_size(v_tail_2764_);
v___x_2767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2765_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
v___x_2768_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2763_, v___x_2767_, v___x_2765_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_PersistentArray_stats___redArg(v_r_2769_);
lean_dec_ref(v_r_2769_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2771_, lean_object* v_r_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_PersistentArray_stats___redArg(v_r_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_r_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_PersistentArray_stats(v_00_u03b1_2774_, v_r_2775_);
lean_dec_ref(v_r_2775_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2781_){
_start:
{
lean_object* v_numNodes_2782_; lean_object* v_depth_2783_; lean_object* v_tailSize_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_numNodes_2782_ = lean_ctor_get(v_s_2781_, 0);
lean_inc(v_numNodes_2782_);
v_depth_2783_ = lean_ctor_get(v_s_2781_, 1);
lean_inc(v_depth_2783_);
v_tailSize_2784_ = lean_ctor_get(v_s_2781_, 2);
lean_inc(v_tailSize_2784_);
lean_dec_ref(v_s_2781_);
v___x_2785_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2786_ = l_Nat_reprFast(v_numNodes_2782_);
v___x_2787_ = lean_string_append(v___x_2785_, v___x_2786_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2789_ = lean_string_append(v___x_2787_, v___x_2788_);
v___x_2790_ = l_Nat_reprFast(v_depth_2783_);
v___x_2791_ = lean_string_append(v___x_2789_, v___x_2790_);
lean_dec_ref(v___x_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2793_ = lean_string_append(v___x_2791_, v___x_2792_);
v___x_2794_ = l_Nat_reprFast(v_tailSize_2784_);
v___x_2795_ = lean_string_append(v___x_2793_, v___x_2794_);
lean_dec_ref(v___x_2794_);
v___x_2796_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2797_ = lean_string_append(v___x_2795_, v___x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2800_, lean_object* v_j_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_zero_2803_; uint8_t v_isZero_2804_; 
v_zero_2803_ = lean_unsigned_to_nat(0u);
v_isZero_2804_ = lean_nat_dec_eq(v_j_2801_, v_zero_2803_);
if (v_isZero_2804_ == 1)
{
lean_dec(v_j_2801_);
lean_dec(v_v_2800_);
return v_a_2802_;
}
else
{
lean_object* v_one_2805_; lean_object* v_n_2806_; lean_object* v___x_2807_; 
v_one_2805_ = lean_unsigned_to_nat(1u);
v_n_2806_ = lean_nat_sub(v_j_2801_, v_one_2805_);
lean_dec(v_j_2801_);
lean_inc(v_v_2800_);
v___x_2807_ = l_Lean_PersistentArray_push___redArg(v_a_2802_, v_v_2800_);
v_j_2801_ = v_n_2806_;
v_a_2802_ = v___x_2807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2809_, lean_object* v_v_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2812_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2810_, v_n_2809_, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2813_, lean_object* v_n_2814_, lean_object* v_v_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_mkPersistentArray___redArg(v_n_2814_, v_v_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2817_, lean_object* v_v_2818_, lean_object* v_n_2819_, lean_object* v_j_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2818_, v_j_2820_, v_a_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_v_2825_, lean_object* v_n_2826_, lean_object* v_j_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2824_, v_v_2825_, v_n_2826_, v_j_2827_, v_a_2828_, v_a_2829_);
lean_dec(v_n_2826_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2831_, lean_object* v_v_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_mkPersistentArray___redArg(v_n_2831_, v_v_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2834_, lean_object* v_n_2835_, lean_object* v_v_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_mkPersistentArray___redArg(v_n_2835_, v_v_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
if (lean_obj_tag(v_a_2838_) == 0)
{
return v_a_2839_;
}
else
{
lean_object* v_head_2840_; lean_object* v_tail_2841_; lean_object* v___x_2842_; 
v_head_2840_ = lean_ctor_get(v_a_2838_, 0);
lean_inc(v_head_2840_);
v_tail_2841_ = lean_ctor_get(v_a_2838_, 1);
lean_inc(v_tail_2841_);
lean_dec_ref_known(v_a_2838_, 2);
v___x_2842_ = l_Lean_PersistentArray_push___redArg(v_a_2839_, v_head_2840_);
v_a_2838_ = v_tail_2841_;
v_a_2839_ = v___x_2842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object* v_00_u03b1_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_a_2845_, v_a_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object* v_xs_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = lean_unsigned_to_nat(32u);
v___x_2850_ = lean_mk_empty_array_with_capacity(v___x_2849_);
lean_dec_ref(v___x_2850_);
v___x_2851_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_2852_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_xs_2848_, v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object* v_00_u03b1_2853_, lean_object* v_xs_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_List_toPArray_x27___redArg(v_xs_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object* v_xs_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2857_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_array_get_size(v_xs_2856_);
v___x_2860_ = lean_nat_dec_lt(v___x_2858_, v___x_2859_);
if (v___x_2860_ == 0)
{
return v___x_2857_;
}
else
{
size_t v___x_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = lean_usize_of_nat(v___x_2859_);
v___x_2863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2856_, v___x_2861_, v___x_2862_, v___x_2857_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2864_);
lean_dec_ref(v_xs_2864_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object* v_00_u03b1_2866_, lean_object* v_xs_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_2869_, lean_object* v_xs_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Array_toPArray_x27(v_00_u03b1_2869_, v_xs_2870_);
lean_dec_ref(v_xs_2870_);
return v_res_2871_;
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
