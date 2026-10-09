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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg(){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__1));
return v___x_52_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPersistentArrayNode_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_53_;
v_res_53_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
stack->m_obj
 = v_res_53_;
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
lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg(){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPersistentArrayNode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_61_;
v_res_61_ = l_Lean_instInhabitedPersistentArrayNode___redArg();
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg___boxed(lean_object* v___dummy_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_instInhabitedPersistentArrayNode___redArg();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_65_;
}
}
uint8_t l_Lean_PersistentArrayNode_isNode___redArg(lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 1;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArrayNode_isNode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_66_ = stack[0].m_obj;
uint8_t v_res_69_;
v_res_69_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_66_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___redArg___boxed(lean_object* v_x_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_70_);
lean_dec_ref(v_x_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
uint8_t l_Lean_PersistentArrayNode_isNode(lean_object* v_00_u03b1_73_, lean_object* v_x_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Lean_PersistentArrayNode_isNode_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_74_ = stack[1].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_Lean_PersistentArrayNode_isNode(lean_box(0), v_x_74_);
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___boxed(lean_object* v_00_u03b1_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_PersistentArrayNode_isNode(v_00_u03b1_77_, v_x_78_);
lean_dec_ref(v_x_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
static size_t _init_l_Lean_PersistentArray_initShift(void){
_start:
{
size_t v___x_81_; 
v___x_81_ = ((size_t)5ULL);
return v___x_81_;
}
}
static size_t _init_l_Lean_PersistentArray_branching(void){
_start:
{
size_t v___x_82_; 
v___x_82_ = ((size_t)32ULL);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_unsigned_to_nat(32u);
v___x_84_ = lean_mk_empty_array_with_capacity(v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1(void){
_start:
{
size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_86_ = ((size_t)5ULL);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_unsigned_to_nat(32u);
v___x_89_ = lean_mk_empty_array_with_capacity(v___x_88_);
v___x_90_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__0, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__0);
v___x_91_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_87_);
lean_ctor_set(v___x_91_, 3, v___x_87_);
lean_ctor_set_usize(v___x_91_, 4, v___x_86_);
return v___x_91_;
}
}
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg(){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
return v___x_93_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPersistentArray_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_94_;
v_res_94_ = l_Lean_instInhabitedPersistentArray_default___redArg();
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v_res_96_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___closed__0(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object* v_00_u03b1_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_99_;
}
}
lean_object* l_Lean_instInhabitedPersistentArray___redArg(){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_101_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPersistentArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_102_;
v_res_102_ = l_Lean_instInhabitedPersistentArray___redArg();
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg___boxed(lean_object* v___dummy_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_instInhabitedPersistentArray___redArg();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_106_;
}
}
lean_object* l_Lean_PersistentArray_empty___redArg(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(32u);
v___x_109_ = lean_mk_empty_array_with_capacity(v___x_108_);
lean_dec_ref(v___x_109_);
v___x_110_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_111_;
v_res_111_ = l_Lean_PersistentArray_empty___redArg();
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg___boxed(lean_object* v___dummy_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_PersistentArray_empty___redArg();
return v_res_113_;
}
}
static lean_object* _init_l_Lean_PersistentArray_empty___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentArray_empty___redArg();
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object* v_00_u03b1_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
return v___x_116_;
}
}
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object* v_a_117_){
_start:
{
lean_object* v_size_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_size_118_ = lean_ctor_get(v_a_117_, 2);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_eq(v_size_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_117_ = stack[0].m_obj;
uint8_t v_res_121_;
v_res_121_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_117_);
stack->m_num = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object* v_a_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_122_);
lean_dec_ref(v_a_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
uint8_t l_Lean_PersistentArray_isEmpty(lean_object* v_00_u03b1_125_, lean_object* v_a_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_126_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_126_ = stack[1].m_obj;
uint8_t v_res_128_;
v_res_128_ = l_Lean_PersistentArray_isEmpty(lean_box(0), v_a_126_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object* v_00_u03b1_129_, lean_object* v_a_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_129_, v_a_130_);
lean_dec_ref(v_a_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(32u);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mkEmptyArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_136_;
v_res_136_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg___boxed(lean_object* v___dummy_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
return v_res_138_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkEmptyArray___closed__0(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray(lean_object* v_00_u03b1_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
return v___x_141_;
}
}
size_t l_Lean_PersistentArray_mul2Shift(size_t v_i_142_, size_t v_shift_143_){
_start:
{
size_t v___x_144_; 
v___x_144_ = lean_usize_shift_left(v_i_142_, v_shift_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mul2Shift_0interp(lean_interpreter_value* stack)
{
size_t v_i_142_ = stack[0].m_num;
size_t v_shift_143_ = stack[1].m_num;
size_t v_res_145_;
v_res_145_ = l_Lean_PersistentArray_mul2Shift(v_i_142_, v_shift_143_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mul2Shift___boxed(lean_object* v_i_146_, lean_object* v_shift_147_){
_start:
{
size_t v_i_boxed_148_; size_t v_shift_boxed_149_; size_t v_res_150_; lean_object* v_r_151_; 
v_i_boxed_148_ = lean_unbox_usize(v_i_146_);
lean_dec(v_i_146_);
v_shift_boxed_149_ = lean_unbox_usize(v_shift_147_);
lean_dec(v_shift_147_);
v_res_150_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_148_, v_shift_boxed_149_);
v_r_151_ = lean_box_usize(v_res_150_);
return v_r_151_;
}
}
size_t l_Lean_PersistentArray_div2Shift(size_t v_i_152_, size_t v_shift_153_){
_start:
{
size_t v___x_154_; 
v___x_154_ = lean_usize_shift_right(v_i_152_, v_shift_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_div2Shift_0interp(lean_interpreter_value* stack)
{
size_t v_i_152_ = stack[0].m_num;
size_t v_shift_153_ = stack[1].m_num;
size_t v_res_155_;
v_res_155_ = l_Lean_PersistentArray_div2Shift(v_i_152_, v_shift_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_div2Shift___boxed(lean_object* v_i_156_, lean_object* v_shift_157_){
_start:
{
size_t v_i_boxed_158_; size_t v_shift_boxed_159_; size_t v_res_160_; lean_object* v_r_161_; 
v_i_boxed_158_ = lean_unbox_usize(v_i_156_);
lean_dec(v_i_156_);
v_shift_boxed_159_ = lean_unbox_usize(v_shift_157_);
lean_dec(v_shift_157_);
v_res_160_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_158_, v_shift_boxed_159_);
v_r_161_ = lean_box_usize(v_res_160_);
return v_r_161_;
}
}
size_t l_Lean_PersistentArray_mod2Shift(size_t v_i_162_, size_t v_shift_163_){
_start:
{
size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; 
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_shift_left(v___x_164_, v_shift_163_);
v___x_166_ = lean_usize_sub(v___x_165_, v___x_164_);
v___x_167_ = lean_usize_land(v_i_162_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mod2Shift_0interp(lean_interpreter_value* stack)
{
size_t v_i_162_ = stack[0].m_num;
size_t v_shift_163_ = stack[1].m_num;
size_t v_res_168_;
v_res_168_ = l_Lean_PersistentArray_mod2Shift(v_i_162_, v_shift_163_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mod2Shift___boxed(lean_object* v_i_169_, lean_object* v_shift_170_){
_start:
{
size_t v_i_boxed_171_; size_t v_shift_boxed_172_; size_t v_res_173_; lean_object* v_r_174_; 
v_i_boxed_171_ = lean_unbox_usize(v_i_169_);
lean_dec(v_i_169_);
v_shift_boxed_172_ = lean_unbox_usize(v_shift_170_);
lean_dec(v_shift_170_);
v_res_173_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_171_, v_shift_boxed_172_);
v_r_174_ = lean_box_usize(v_res_173_);
return v_r_174_;
}
}
lean_object* l_Lean_PersistentArray_getAux___redArg(lean_object* v_inst_175_, lean_object* v_x_176_, size_t v_x_177_, size_t v_x_178_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
lean_object* v_cs_179_; lean_object* v___x_180_; size_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; 
v_cs_179_ = lean_ctor_get(v_x_176_, 0);
v___x_180_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_181_ = lean_usize_shift_right(v_x_177_, v_x_178_);
v___x_182_ = lean_usize_to_nat(v___x_181_);
v___x_183_ = lean_array_get_borrowed(v___x_180_, v_cs_179_, v___x_182_);
lean_dec(v___x_182_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_shift_left(v___x_184_, v_x_178_);
v___x_186_ = lean_usize_sub(v___x_185_, v___x_184_);
v___x_187_ = lean_usize_land(v_x_177_, v___x_186_);
v___x_188_ = ((size_t)5ULL);
v___x_189_ = lean_usize_sub(v_x_178_, v___x_188_);
v_x_176_ = v___x_183_;
v_x_177_ = v___x_187_;
v_x_178_ = v___x_189_;
goto _start;
}
else
{
lean_object* v_vs_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_vs_191_ = lean_ctor_get(v_x_176_, 0);
v___x_192_ = lean_usize_to_nat(v_x_177_);
v___x_193_ = lean_array_get_borrowed(v_inst_175_, v_vs_191_, v___x_192_);
lean_dec(v___x_192_);
lean_inc(v___x_193_);
return v___x_193_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_getAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_175_ = stack[0].m_obj;
lean_object* v_x_176_ = stack[1].m_obj;
size_t v_x_177_ = stack[2].m_num;
size_t v_x_178_ = stack[3].m_num;
lean_object* v_res_194_;
v_res_194_ = l_Lean_PersistentArray_getAux___redArg(v_inst_175_, v_x_176_, v_x_177_, v_x_178_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg___boxed(lean_object* v_inst_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_94__boxed_199_; size_t v_x_95__boxed_200_; lean_object* v_res_201_; 
v_x_94__boxed_199_ = lean_unbox_usize(v_x_197_);
lean_dec(v_x_197_);
v_x_95__boxed_200_ = lean_unbox_usize(v_x_198_);
lean_dec(v_x_198_);
v_res_201_ = l_Lean_PersistentArray_getAux___redArg(v_inst_195_, v_x_196_, v_x_94__boxed_199_, v_x_95__boxed_200_);
lean_dec_ref(v_x_196_);
lean_dec(v_inst_195_);
return v_res_201_;
}
}
lean_object* l_Lean_PersistentArray_getAux(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_x_204_, size_t v_x_205_, size_t v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_PersistentArray_getAux___redArg(v_inst_203_, v_x_204_, v_x_205_, v_x_206_);
return v___x_207_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_getAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_203_ = stack[1].m_obj;
lean_object* v_x_204_ = stack[2].m_obj;
size_t v_x_205_ = stack[3].m_num;
size_t v_x_206_ = stack[4].m_num;
lean_object* v_res_208_;
v_res_208_ = l_Lean_PersistentArray_getAux(lean_box(0), v_inst_203_, v_x_204_, v_x_205_, v_x_206_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___boxed(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
size_t v_x_159__boxed_214_; size_t v_x_160__boxed_215_; lean_object* v_res_216_; 
v_x_159__boxed_214_ = lean_unbox_usize(v_x_212_);
lean_dec(v_x_212_);
v_x_160__boxed_215_ = lean_unbox_usize(v_x_213_);
lean_dec(v_x_213_);
v_res_216_ = l_Lean_PersistentArray_getAux(v_00_u03b1_209_, v_inst_210_, v_x_211_, v_x_159__boxed_214_, v_x_160__boxed_215_);
lean_dec_ref(v_x_211_);
lean_dec(v_inst_210_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object* v_inst_217_, lean_object* v_t_218_, lean_object* v_i_219_){
_start:
{
lean_object* v_root_220_; lean_object* v_tail_221_; size_t v_shift_222_; lean_object* v_tailOff_223_; uint8_t v___x_224_; 
v_root_220_ = lean_ctor_get(v_t_218_, 0);
v_tail_221_ = lean_ctor_get(v_t_218_, 1);
v_shift_222_ = lean_ctor_get_usize(v_t_218_, 4);
v_tailOff_223_ = lean_ctor_get(v_t_218_, 3);
v___x_224_ = lean_nat_dec_le(v_tailOff_223_, v_i_219_);
if (v___x_224_ == 0)
{
size_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_usize_of_nat(v_i_219_);
v___x_226_ = l_Lean_PersistentArray_getAux___redArg(v_inst_217_, v_root_220_, v___x_225_, v_shift_222_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_nat_sub(v_i_219_, v_tailOff_223_);
v___x_228_ = lean_array_get_borrowed(v_inst_217_, v_tail_221_, v___x_227_);
lean_dec(v___x_227_);
lean_inc(v___x_228_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg___boxed(lean_object* v_inst_229_, lean_object* v_t_230_, lean_object* v_i_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_229_, v_t_230_, v_i_231_);
lean_dec(v_i_231_);
lean_dec_ref(v_t_230_);
lean_dec(v_inst_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21(lean_object* v_00_u03b1_233_, lean_object* v_inst_234_, lean_object* v_t_235_, lean_object* v_i_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_234_, v_t_235_, v_i_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___boxed(lean_object* v_00_u03b1_238_, lean_object* v_inst_239_, lean_object* v_t_240_, lean_object* v_i_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_PersistentArray_get_x21(v_00_u03b1_238_, v_inst_239_, v_t_240_, v_i_241_);
lean_dec(v_i_241_);
lean_dec_ref(v_t_240_);
lean_dec(v_inst_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(lean_object* v_inst_243_, lean_object* v_xs_244_, lean_object* v_i_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_243_, v_xs_244_, v_i_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(lean_object* v_inst_248_, lean_object* v_xs_249_, lean_object* v_i_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(v_inst_248_, v_xs_249_, v_i_250_, v_x_251_);
lean_dec(v_i_250_);
lean_dec_ref(v_xs_249_);
lean_dec(v_inst_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(lean_object* v_inst_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_254_, 0, v_inst_253_);
return v___f_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(lean_object* v_00_u03b1_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___f_257_; 
v___f_257_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_257_, 0, v_inst_256_);
return v___f_257_;
}
}
lean_object* l_Lean_PersistentArray_setAux___redArg(lean_object* v_x_258_, size_t v_x_259_, size_t v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v_cs_262_; size_t v_j_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_cs_262_ = lean_ctor_get(v_x_258_, 0);
v_j_263_ = lean_usize_shift_right(v_x_259_, v_x_260_);
v___x_264_ = lean_usize_to_nat(v_j_263_);
v___x_265_ = lean_array_get_size(v_cs_262_);
v___x_266_ = lean_nat_dec_lt(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_dec(v___x_264_);
lean_dec(v_x_261_);
return v_x_258_;
}
else
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_284_; 
lean_inc_ref(v_cs_262_);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v_x_258_, 0);
lean_dec(v_unused_285_);
v___x_268_ = v_x_258_;
v_isShared_269_ = v_isSharedCheck_284_;
goto v_resetjp_267_;
}
else
{
lean_dec(v_x_258_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_284_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v_i_273_; size_t v___x_274_; size_t v_shift_275_; lean_object* v_v_276_; lean_object* v___x_277_; lean_object* v_xs_x27_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_shift_left(v___x_270_, v_x_260_);
v___x_272_ = lean_usize_sub(v___x_271_, v___x_270_);
v_i_273_ = lean_usize_land(v_x_259_, v___x_272_);
v___x_274_ = ((size_t)5ULL);
v_shift_275_ = lean_usize_sub(v_x_260_, v___x_274_);
v_v_276_ = lean_array_fget(v_cs_262_, v___x_264_);
v___x_277_ = lean_box(0);
v_xs_x27_278_ = lean_array_fset(v_cs_262_, v___x_264_, v___x_277_);
v___x_279_ = l_Lean_PersistentArray_setAux___redArg(v_v_276_, v_i_273_, v_shift_275_, v_x_261_);
v___x_280_ = lean_array_fset(v_xs_x27_278_, v___x_264_, v___x_279_);
lean_dec(v___x_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_280_);
v___x_282_ = v___x_268_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_object* v_vs_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_295_; 
v_vs_286_ = lean_ctor_get(v_x_258_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_295_ == 0)
{
v___x_288_ = v_x_258_;
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_vs_286_);
lean_dec(v_x_258_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_290_ = lean_usize_to_nat(v_x_259_);
v___x_291_ = lean_array_set(v_vs_286_, v___x_290_, v_x_261_);
lean_dec(v___x_290_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_setAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_258_ = stack[0].m_obj;
size_t v_x_259_ = stack[1].m_num;
size_t v_x_260_ = stack[2].m_num;
lean_object* v_x_261_ = stack[3].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_PersistentArray_setAux___redArg(v_x_258_, v_x_259_, v_x_260_, v_x_261_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg___boxed(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
size_t v_x_79__boxed_301_; size_t v_x_80__boxed_302_; lean_object* v_res_303_; 
v_x_79__boxed_301_ = lean_unbox_usize(v_x_298_);
lean_dec(v_x_298_);
v_x_80__boxed_302_ = lean_unbox_usize(v_x_299_);
lean_dec(v_x_299_);
v_res_303_ = l_Lean_PersistentArray_setAux___redArg(v_x_297_, v_x_79__boxed_301_, v_x_80__boxed_302_, v_x_300_);
return v_res_303_;
}
}
lean_object* l_Lean_PersistentArray_setAux(lean_object* v_00_u03b1_304_, lean_object* v_x_305_, size_t v_x_306_, size_t v_x_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_PersistentArray_setAux___redArg(v_x_305_, v_x_306_, v_x_307_, v_x_308_);
return v___x_309_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_setAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_305_ = stack[1].m_obj;
size_t v_x_306_ = stack[2].m_num;
size_t v_x_307_ = stack[3].m_num;
lean_object* v_x_308_ = stack[4].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Lean_PersistentArray_setAux(lean_box(0), v_x_305_, v_x_306_, v_x_307_, v_x_308_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___boxed(lean_object* v_00_u03b1_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
size_t v_x_186__boxed_316_; size_t v_x_187__boxed_317_; lean_object* v_res_318_; 
v_x_186__boxed_316_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_x_187__boxed_317_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_318_ = l_Lean_PersistentArray_setAux(v_00_u03b1_311_, v_x_312_, v_x_186__boxed_316_, v_x_187__boxed_317_, v_x_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg(lean_object* v_t_319_, lean_object* v_i_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_root_322_; lean_object* v_tail_323_; lean_object* v_size_324_; size_t v_shift_325_; lean_object* v_tailOff_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_341_; 
v_root_322_ = lean_ctor_get(v_t_319_, 0);
v_tail_323_ = lean_ctor_get(v_t_319_, 1);
v_size_324_ = lean_ctor_get(v_t_319_, 2);
v_shift_325_ = lean_ctor_get_usize(v_t_319_, 4);
v_tailOff_326_ = lean_ctor_get(v_t_319_, 3);
v_isSharedCheck_341_ = !lean_is_exclusive(v_t_319_);
if (v_isSharedCheck_341_ == 0)
{
v___x_328_ = v_t_319_;
v_isShared_329_ = v_isSharedCheck_341_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_tailOff_326_);
lean_inc(v_size_324_);
lean_inc(v_tail_323_);
lean_inc(v_root_322_);
lean_dec(v_t_319_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_341_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_le(v_tailOff_326_, v_i_320_);
if (v___x_330_ == 0)
{
size_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = lean_usize_of_nat(v_i_320_);
v___x_332_ = l_Lean_PersistentArray_setAux___redArg(v_root_322_, v___x_331_, v_shift_325_, v_a_321_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_332_);
v___x_334_ = v___x_328_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_tail_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_tailOff_326_);
lean_ctor_set_usize(v_reuseFailAlloc_335_, 4, v_shift_325_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_nat_sub(v_i_320_, v_tailOff_326_);
v___x_337_ = lean_array_set(v_tail_323_, v___x_336_, v_a_321_);
lean_dec(v___x_336_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_337_);
v___x_339_ = v___x_328_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_root_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_tailOff_326_);
lean_ctor_set_usize(v_reuseFailAlloc_340_, 4, v_shift_325_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg___boxed(lean_object* v_t_342_, lean_object* v_i_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_PersistentArray_set___redArg(v_t_342_, v_i_343_, v_a_344_);
lean_dec(v_i_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set(lean_object* v_00_u03b1_346_, lean_object* v_t_347_, lean_object* v_i_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_PersistentArray_set___redArg(v_t_347_, v_i_348_, v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___boxed(lean_object* v_00_u03b1_351_, lean_object* v_t_352_, lean_object* v_i_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_PersistentArray_set(v_00_u03b1_351_, v_t_352_, v_i_353_, v_a_354_);
lean_dec(v_i_353_);
return v_res_355_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___redArg(lean_object* v_f_356_, lean_object* v_x_357_, size_t v_x_358_, size_t v_x_359_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v_cs_360_; size_t v_j_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_cs_360_ = lean_ctor_get(v_x_357_, 0);
v_j_361_ = lean_usize_shift_right(v_x_358_, v_x_359_);
v___x_362_ = lean_usize_to_nat(v_j_361_);
v___x_363_ = lean_array_get_size(v_cs_360_);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec(v___x_362_);
lean_dec(v_f_356_);
return v_x_357_;
}
else
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_382_; 
lean_inc_ref(v_cs_360_);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_x_357_, 0);
lean_dec(v_unused_383_);
v___x_366_ = v_x_357_;
v_isShared_367_ = v_isSharedCheck_382_;
goto v_resetjp_365_;
}
else
{
lean_dec(v_x_357_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_382_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v_i_371_; size_t v___x_372_; size_t v_shift_373_; lean_object* v_v_374_; lean_object* v___x_375_; lean_object* v_xs_x27_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_shift_left(v___x_368_, v_x_359_);
v___x_370_ = lean_usize_sub(v___x_369_, v___x_368_);
v_i_371_ = lean_usize_land(v_x_358_, v___x_370_);
v___x_372_ = ((size_t)5ULL);
v_shift_373_ = lean_usize_sub(v_x_359_, v___x_372_);
v_v_374_ = lean_array_fget(v_cs_360_, v___x_362_);
v___x_375_ = lean_box(0);
v_xs_x27_376_ = lean_array_fset(v_cs_360_, v___x_362_, v___x_375_);
v___x_377_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_356_, v_v_374_, v_i_371_, v_shift_373_);
v___x_378_ = lean_array_fset(v_xs_x27_376_, v___x_362_, v___x_377_);
lean_dec(v___x_362_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_378_);
v___x_380_ = v___x_366_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_vs_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_vs_384_ = lean_ctor_get(v_x_357_, 0);
v___x_385_ = lean_usize_to_nat(v_x_358_);
v___x_386_ = lean_array_get_size(v_vs_384_);
v___x_387_ = lean_nat_dec_lt(v___x_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_dec(v___x_385_);
lean_dec(v_f_356_);
return v_x_357_;
}
else
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
lean_inc_ref(v_vs_384_);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v_x_357_, 0);
lean_dec(v_unused_400_);
v___x_389_ = v_x_357_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_x_357_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_v_391_; lean_object* v___x_392_; lean_object* v_xs_x27_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v_v_391_ = lean_array_fget(v_vs_384_, v___x_385_);
v___x_392_ = lean_box(0);
v_xs_x27_393_ = lean_array_fset(v_vs_384_, v___x_385_, v___x_392_);
v___x_394_ = lean_apply_1(v_f_356_, v_v_391_);
v___x_395_ = lean_array_fset(v_xs_x27_393_, v___x_385_, v___x_394_);
lean_dec(v___x_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_395_);
v___x_397_ = v___x_389_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_356_ = stack[0].m_obj;
lean_object* v_x_357_ = stack[1].m_obj;
size_t v_x_358_ = stack[2].m_num;
size_t v_x_359_ = stack[3].m_num;
lean_object* v_res_401_;
v_res_401_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_356_, v_x_357_, v_x_358_, v_x_359_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg___boxed(lean_object* v_f_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
size_t v_x_96__boxed_406_; size_t v_x_97__boxed_407_; lean_object* v_res_408_; 
v_x_96__boxed_406_ = lean_unbox_usize(v_x_404_);
lean_dec(v_x_404_);
v_x_97__boxed_407_ = lean_unbox_usize(v_x_405_);
lean_dec(v_x_405_);
v_res_408_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_402_, v_x_403_, v_x_96__boxed_406_, v_x_97__boxed_407_);
return v_res_408_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_f_411_, lean_object* v_x_412_, size_t v_x_413_, size_t v_x_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_411_, v_x_412_, v_x_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_410_ = stack[1].m_obj;
lean_object* v_f_411_ = stack[2].m_obj;
lean_object* v_x_412_ = stack[3].m_obj;
size_t v_x_413_ = stack[4].m_num;
size_t v_x_414_ = stack[5].m_num;
lean_object* v_res_416_;
v_res_416_ = l_Lean_PersistentArray_modifyAux(lean_box(0), v_inst_410_, v_f_411_, v_x_412_, v_x_413_, v_x_414_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___boxed(lean_object* v_00_u03b1_417_, lean_object* v_inst_418_, lean_object* v_f_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
size_t v_x_214__boxed_423_; size_t v_x_215__boxed_424_; lean_object* v_res_425_; 
v_x_214__boxed_423_ = lean_unbox_usize(v_x_421_);
lean_dec(v_x_421_);
v_x_215__boxed_424_ = lean_unbox_usize(v_x_422_);
lean_dec(v_x_422_);
v_res_425_ = l_Lean_PersistentArray_modifyAux(v_00_u03b1_417_, v_inst_418_, v_f_419_, v_x_420_, v_x_214__boxed_423_, v_x_215__boxed_424_);
lean_dec(v_inst_418_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg(lean_object* v_t_426_, lean_object* v_i_427_, lean_object* v_f_428_){
_start:
{
lean_object* v_root_429_; lean_object* v_tail_430_; lean_object* v_size_431_; size_t v_shift_432_; lean_object* v_tailOff_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_457_; 
v_root_429_ = lean_ctor_get(v_t_426_, 0);
v_tail_430_ = lean_ctor_get(v_t_426_, 1);
v_size_431_ = lean_ctor_get(v_t_426_, 2);
v_shift_432_ = lean_ctor_get_usize(v_t_426_, 4);
v_tailOff_433_ = lean_ctor_get(v_t_426_, 3);
v_isSharedCheck_457_ = !lean_is_exclusive(v_t_426_);
if (v_isSharedCheck_457_ == 0)
{
v___x_435_ = v_t_426_;
v_isShared_436_ = v_isSharedCheck_457_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_tailOff_433_);
lean_inc(v_size_431_);
lean_inc(v_tail_430_);
lean_inc(v_root_429_);
lean_dec(v_t_426_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_457_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_le(v_tailOff_433_, v_i_427_);
if (v___x_437_ == 0)
{
size_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_usize_of_nat(v_i_427_);
v___x_439_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_428_, v_root_429_, v___x_438_, v_shift_432_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_439_);
v___x_441_ = v___x_435_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_tail_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_size_431_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_tailOff_433_);
lean_ctor_set_usize(v_reuseFailAlloc_442_, 4, v_shift_432_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_nat_sub(v_i_427_, v_tailOff_433_);
v___x_444_ = lean_array_get_size(v_tail_430_);
v___x_445_ = lean_nat_dec_lt(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v___x_443_);
lean_dec(v_f_428_);
if (v_isShared_436_ == 0)
{
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_root_429_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_tail_430_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_size_431_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_tailOff_433_);
lean_ctor_set_usize(v_reuseFailAlloc_448_, 4, v_shift_432_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
else
{
lean_object* v_v_449_; lean_object* v___x_450_; lean_object* v_xs_x27_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v_v_449_ = lean_array_fget(v_tail_430_, v___x_443_);
v___x_450_ = lean_box(0);
v_xs_x27_451_ = lean_array_fset(v_tail_430_, v___x_443_, v___x_450_);
v___x_452_ = lean_apply_1(v_f_428_, v_v_449_);
v___x_453_ = lean_array_fset(v_xs_x27_451_, v___x_443_, v___x_452_);
lean_dec(v___x_443_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_453_);
v___x_455_ = v___x_435_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_root_429_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_size_431_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_tailOff_433_);
lean_ctor_set_usize(v_reuseFailAlloc_456_, 4, v_shift_432_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg___boxed(lean_object* v_t_458_, lean_object* v_i_459_, lean_object* v_f_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_PersistentArray_modify___redArg(v_t_458_, v_i_459_, v_f_460_);
lean_dec(v_i_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify(lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_t_464_, lean_object* v_i_465_, lean_object* v_f_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentArray_modify___redArg(v_t_464_, v_i_465_, v_f_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___boxed(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_t_470_, lean_object* v_i_471_, lean_object* v_f_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_PersistentArray_modify(v_00_u03b1_468_, v_inst_469_, v_t_470_, v_i_471_, v_f_472_);
lean_dec(v_i_471_);
lean_dec(v_inst_469_);
return v_res_473_;
}
}
lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t v_shift_474_, lean_object* v_a_475_){
_start:
{
size_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((size_t)0ULL);
v___x_477_ = lean_usize_dec_eq(v_shift_474_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_478_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v___x_479_ = ((size_t)5ULL);
v___x_480_ = lean_usize_sub(v_shift_474_, v___x_479_);
v___x_481_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_480_, v_a_475_);
v___x_482_ = lean_array_push(v___x_478_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_a_475_);
return v___x_484_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mkNewPath___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_shift_474_ = stack[0].m_num;
lean_object* v_a_475_ = stack[1].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_474_, v_a_475_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg___boxed(lean_object* v_shift_486_, lean_object* v_a_487_){
_start:
{
size_t v_shift_boxed_488_; lean_object* v_res_489_; 
v_shift_boxed_488_ = lean_unbox_usize(v_shift_486_);
lean_dec(v_shift_486_);
v_res_489_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_488_, v_a_487_);
return v_res_489_;
}
}
lean_object* l_Lean_PersistentArray_mkNewPath(lean_object* v_00_u03b1_490_, size_t v_shift_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_491_, v_a_492_);
return v___x_493_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mkNewPath_0interp(lean_interpreter_value* stack)
{
size_t v_shift_491_ = stack[1].m_num;
lean_object* v_a_492_ = stack[2].m_obj;
lean_object* v_res_494_;
v_res_494_ = l_Lean_PersistentArray_mkNewPath(lean_box(0), v_shift_491_, v_a_492_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___boxed(lean_object* v_00_u03b1_495_, lean_object* v_shift_496_, lean_object* v_a_497_){
_start:
{
size_t v_shift_boxed_498_; lean_object* v_res_499_; 
v_shift_boxed_498_ = lean_unbox_usize(v_shift_496_);
lean_dec(v_shift_496_);
v_res_499_ = l_Lean_PersistentArray_mkNewPath(v_00_u03b1_495_, v_shift_boxed_498_, v_a_497_);
return v_res_499_;
}
}
lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object* v_x_500_, size_t v_x_501_, size_t v_x_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v_cs_504_; size_t v___x_505_; uint8_t v___x_506_; 
v_cs_504_ = lean_ctor_get(v_x_500_, 0);
v___x_505_ = ((size_t)32ULL);
v___x_506_ = lean_usize_dec_lt(v_x_501_, v___x_505_);
if (v___x_506_ == 0)
{
size_t v_j_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v_shift_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_j_507_ = lean_usize_shift_right(v_x_501_, v_x_502_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_shift_left(v___x_508_, v_x_502_);
v___x_510_ = ((size_t)5ULL);
v_shift_511_ = lean_usize_sub(v_x_502_, v___x_510_);
v___x_512_ = lean_usize_to_nat(v_j_507_);
v___x_513_ = lean_array_get_size(v_cs_504_);
v___x_514_ = lean_nat_dec_lt(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_523_; 
lean_inc_ref(v_cs_504_);
lean_dec(v___x_512_);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_x_500_, 0);
lean_dec(v_unused_524_);
v___x_516_ = v_x_500_;
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_x_500_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_518_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_511_, v_x_503_);
v___x_519_ = lean_array_push(v_cs_504_, v___x_518_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_519_);
v___x_521_ = v___x_516_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
if (v___x_514_ == 0)
{
lean_dec(v___x_512_);
lean_dec_ref(v_x_503_);
return v_x_500_;
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_538_; 
lean_inc_ref(v_cs_504_);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_x_500_, 0);
lean_dec(v_unused_539_);
v___x_526_ = v_x_500_;
v_isShared_527_ = v_isSharedCheck_538_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_x_500_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_538_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
size_t v___x_528_; size_t v_i_529_; lean_object* v_v_530_; lean_object* v___x_531_; lean_object* v_xs_x27_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_528_ = lean_usize_sub(v___x_509_, v___x_508_);
v_i_529_ = lean_usize_land(v_x_501_, v___x_528_);
v_v_530_ = lean_array_fget(v_cs_504_, v___x_512_);
v___x_531_ = lean_box(0);
v_xs_x27_532_ = lean_array_fset(v_cs_504_, v___x_512_, v___x_531_);
v___x_533_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_v_530_, v_i_529_, v_shift_511_, v_x_503_);
v___x_534_ = lean_array_fset(v_xs_x27_532_, v___x_512_, v___x_533_);
lean_dec(v___x_512_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_534_);
v___x_536_ = v___x_526_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
lean_inc_ref(v_cs_504_);
v_isSharedCheck_548_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_x_500_, 0);
lean_dec(v_unused_549_);
v___x_541_ = v_x_500_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_x_500_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 0, v_x_503_);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_x_503_);
v___x_544_ = v_reuseFailAlloc_547_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_array_push(v_cs_504_, v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
}
else
{
lean_dec_ref(v_x_503_);
return v_x_500_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_insertNewLeaf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_500_ = stack[0].m_obj;
size_t v_x_501_ = stack[1].m_num;
size_t v_x_502_ = stack[2].m_num;
lean_object* v_x_503_ = stack[3].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_500_, v_x_501_, v_x_502_, v_x_503_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
size_t v_x_102__boxed_555_; size_t v_x_103__boxed_556_; lean_object* v_res_557_; 
v_x_102__boxed_555_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_x_103__boxed_556_ = lean_unbox_usize(v_x_553_);
lean_dec(v_x_553_);
v_res_557_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_551_, v_x_102__boxed_555_, v_x_103__boxed_556_, v_x_554_);
return v_res_557_;
}
}
lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object* v_00_u03b1_558_, lean_object* v_x_559_, size_t v_x_560_, size_t v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_559_, v_x_560_, v_x_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_insertNewLeaf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_559_ = stack[1].m_obj;
size_t v_x_560_ = stack[2].m_num;
size_t v_x_561_ = stack[3].m_num;
lean_object* v_x_562_ = stack[4].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_PersistentArray_insertNewLeaf(lean_box(0), v_x_559_, v_x_560_, v_x_561_, v_x_562_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object* v_00_u03b1_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
size_t v_x_245__boxed_570_; size_t v_x_246__boxed_571_; lean_object* v_res_572_; 
v_x_245__boxed_570_ = lean_unbox_usize(v_x_567_);
lean_dec(v_x_567_);
v_x_246__boxed_571_ = lean_unbox_usize(v_x_568_);
lean_dec(v_x_568_);
v_res_572_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_565_, v_x_566_, v_x_245__boxed_570_, v_x_246__boxed_571_, v_x_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object* v_t_575_){
_start:
{
lean_object* v_root_576_; lean_object* v_tail_577_; lean_object* v_size_578_; size_t v_shift_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_606_; 
v_root_576_ = lean_ctor_get(v_t_575_, 0);
v_tail_577_ = lean_ctor_get(v_t_575_, 1);
v_size_578_ = lean_ctor_get(v_t_575_, 2);
v_shift_579_ = lean_ctor_get_usize(v_t_575_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v_t_575_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_t_575_, 3);
lean_dec(v_unused_607_);
v___x_581_ = v_t_575_;
v_isShared_582_ = v_isSharedCheck_606_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_size_578_);
lean_inc(v_tail_577_);
lean_inc(v_root_576_);
lean_dec(v_t_575_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_606_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = ((size_t)5ULL);
v___x_585_ = lean_usize_add(v_shift_579_, v___x_584_);
v___x_586_ = lean_usize_shift_left(v___x_583_, v___x_585_);
v___x_587_ = lean_usize_to_nat(v___x_586_);
v___x_588_ = lean_nat_dec_le(v_size_578_, v___x_587_);
lean_dec(v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v_n_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_589_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v_n_590_ = lean_array_push(v___x_589_, v_root_576_);
v___x_591_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_579_, v_tail_577_);
v___x_592_ = lean_array_push(v_n_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
lean_inc(v_size_578_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 3, v_size_578_);
lean_ctor_set(v___x_581_, 1, v___x_594_);
lean_ctor_set(v___x_581_, 0, v___x_593_);
v___x_596_ = v___x_581_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_size_578_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_size_578_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_ctor_set_usize(v___x_596_, 4, v___x_585_);
return v___x_596_;
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; size_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_sub(v_size_578_, v___x_598_);
v___x_600_ = lean_usize_of_nat(v___x_599_);
lean_dec(v___x_599_);
v___x_601_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_root_576_, v___x_600_, v_shift_579_, v_tail_577_);
v___x_602_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
lean_inc(v_size_578_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 3, v_size_578_);
lean_ctor_set(v___x_581_, 1, v___x_602_);
lean_ctor_set(v___x_581_, 0, v___x_601_);
v___x_604_ = v___x_581_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_size_578_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_size_578_);
lean_ctor_set_usize(v_reuseFailAlloc_605_, 4, v_shift_579_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object* v_00_u03b1_608_, lean_object* v_t_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__0(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = l_System_Platform_numBits;
v___x_612_ = lean_unsigned_to_nat(2u);
v___x_613_ = lean_nat_pow(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(3u);
v___x_615_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__0, &l_Lean_PersistentArray_tooBig___closed__0_once, _init_l_Lean_PersistentArray_tooBig___closed__0);
v___x_616_ = lean_nat_shiftr(v___x_615_, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig(void){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__1, &l_Lean_PersistentArray_tooBig___closed__1_once, _init_l_Lean_PersistentArray_tooBig___closed__1);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object* v_t_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_root_620_; lean_object* v_tail_621_; lean_object* v_size_622_; size_t v_shift_623_; lean_object* v_tailOff_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_640_; 
v_root_620_ = lean_ctor_get(v_t_618_, 0);
v_tail_621_ = lean_ctor_get(v_t_618_, 1);
v_size_622_ = lean_ctor_get(v_t_618_, 2);
v_shift_623_ = lean_ctor_get_usize(v_t_618_, 4);
v_tailOff_624_ = lean_ctor_get(v_t_618_, 3);
v_isSharedCheck_640_ = !lean_is_exclusive(v_t_618_);
if (v_isSharedCheck_640_ == 0)
{
v___x_626_ = v_t_618_;
v_isShared_627_ = v_isSharedCheck_640_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_tailOff_624_);
lean_inc(v_size_622_);
lean_inc(v_tail_621_);
lean_inc(v_root_620_);
lean_dec(v_t_618_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_640_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_r_632_; 
v___x_628_ = lean_array_push(v_tail_621_, v_a_619_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_size_622_, v___x_629_);
lean_inc_ref(v___x_628_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 2, v___x_630_);
lean_ctor_set(v___x_626_, 1, v___x_628_);
v_r_632_ = v___x_626_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_root_620_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_tailOff_624_);
lean_ctor_set_usize(v_reuseFailAlloc_639_, 4, v_shift_623_);
v_r_632_ = v_reuseFailAlloc_639_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_array_get_size(v___x_628_);
lean_dec_ref(v___x_628_);
v___x_634_ = lean_unsigned_to_nat(32u);
v___x_635_ = lean_nat_dec_lt(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = l_Lean_PersistentArray_tooBig;
v___x_637_ = lean_nat_dec_le(v___x_636_, v_size_622_);
lean_dec(v_size_622_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_632_);
return v___x_638_;
}
else
{
return v_r_632_;
}
}
else
{
lean_dec(v_size_622_);
return v_r_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_641_, lean_object* v_t_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentArray_push___redArg(v_t_642_, v_a_643_);
return v___x_644_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg(){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(32u);
v___x_647_ = lean_mk_empty_array_with_capacity(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_648_;
v_res_648_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg___boxed(lean_object* v___dummy_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v_res_650_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0(void){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_cs_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_708_; 
v_cs_658_ = lean_ctor_get(v_x_657_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_708_ == 0)
{
v___x_660_ = v_x_657_;
v_isShared_661_ = v_isSharedCheck_708_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_cs_658_);
lean_dec(v_x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_708_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_array_get_size(v_cs_658_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_eq(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v_idx_666_; lean_object* v_last_667_; lean_object* v___x_668_; lean_object* v_fst_669_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v_idx_666_ = lean_nat_sub(v___x_662_, v___x_665_);
v_last_667_ = lean_array_fget_borrowed(v_cs_658_, v_idx_666_);
lean_inc(v_last_667_);
v___x_668_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_667_);
v_fst_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_fst_669_);
if (lean_obj_tag(v_fst_669_) == 0)
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_idx_666_);
lean_del_object(v___x_660_);
lean_dec_ref(v_cs_658_);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; 
v_unused_678_ = lean_ctor_get(v___x_668_, 1);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v___x_668_, 0);
lean_dec(v_unused_679_);
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_snd_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_705_; 
v_snd_680_ = lean_ctor_get(v___x_668_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_668_, 0);
lean_dec(v_unused_706_);
v___x_682_ = v___x_668_;
v_isShared_683_ = v_isSharedCheck_705_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_snd_680_);
lean_dec(v___x_668_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_705_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v_cs_x27_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_684_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v_cs_x27_685_ = lean_array_fset(v_cs_658_, v_idx_666_, v___x_684_);
v___x_686_ = lean_array_get_size(v_snd_680_);
v___x_687_ = lean_nat_dec_eq(v___x_686_, v___x_663_);
if (v___x_687_ == 0)
{
lean_object* v___x_689_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_snd_680_);
v___x_689_ = v___x_660_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_snd_680_);
v___x_689_ = v_reuseFailAlloc_694_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_array_fset(v_cs_x27_685_, v_idx_666_, v___x_689_);
lean_dec(v_idx_666_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_690_);
v___x_692_ = v___x_682_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v_cs_x27_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
lean_dec(v_snd_680_);
lean_dec(v_idx_666_);
lean_del_object(v___x_660_);
v_cs_x27_695_ = lean_array_pop(v_cs_x27_685_);
v___x_696_ = lean_array_get_size(v_cs_x27_695_);
v___x_697_ = lean_nat_dec_eq(v___x_696_, v___x_663_);
if (v___x_697_ == 0)
{
lean_object* v___x_699_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_cs_x27_695_);
v___x_699_ = v___x_682_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_cs_x27_695_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_dec_ref(v_cs_x27_695_);
v___x_701_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_701_);
v___x_703_ = v___x_682_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
else
{
lean_object* v___x_707_; 
lean_del_object(v___x_660_);
lean_dec_ref(v_cs_658_);
v___x_707_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
return v___x_707_;
}
}
}
else
{
lean_object* v_vs_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_vs_709_ = lean_ctor_get(v_x_657_, 0);
lean_inc_ref(v_vs_709_);
lean_dec_ref_known(v_x_657_, 1);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_vs_709_);
v___x_711_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_713_, lean_object* v_x_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_716_){
_start:
{
lean_object* v_root_717_; lean_object* v_tail_718_; lean_object* v_size_719_; size_t v_shift_720_; lean_object* v_tailOff_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_root_717_ = lean_ctor_get(v_t_716_, 0);
v_tail_718_ = lean_ctor_get(v_t_716_, 1);
v_size_719_ = lean_ctor_get(v_t_716_, 2);
v_shift_720_ = lean_ctor_get_usize(v_t_716_, 4);
v_tailOff_721_ = lean_ctor_get(v_t_716_, 3);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_array_get_size(v_tail_718_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v_fst_726_; 
lean_inc_ref(v_root_717_);
v___x_725_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_717_);
v_fst_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_fst_726_);
if (lean_obj_tag(v_fst_726_) == 0)
{
lean_dec_ref(v___x_725_);
return v_t_716_;
}
else
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_size_719_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_t_716_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; 
v_unused_760_ = lean_ctor_get(v_t_716_, 3);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_t_716_, 2);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_t_716_, 1);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_t_716_, 0);
lean_dec(v_unused_763_);
v___x_728_ = v_t_716_;
v_isShared_729_ = v_isSharedCheck_759_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_t_716_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_759_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_snd_730_; lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_758_; 
v_snd_730_ = lean_ctor_get(v___x_725_, 1);
lean_inc(v_snd_730_);
lean_dec_ref(v___x_725_);
v_val_731_ = lean_ctor_get(v_fst_726_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_fst_726_);
if (v_isSharedCheck_758_ == 0)
{
v___x_733_ = v_fst_726_;
v_isShared_734_ = v_isSharedCheck_758_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v_fst_726_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_758_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_last_735_; lean_object* v___x_736_; lean_object* v_newSize_737_; lean_object* v___x_738_; lean_object* v_newTailOff_739_; uint8_t v___y_741_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_last_735_ = lean_array_pop(v_val_731_);
v___x_736_ = lean_unsigned_to_nat(1u);
v_newSize_737_ = lean_nat_sub(v_size_719_, v___x_736_);
lean_dec(v_size_719_);
v___x_738_ = lean_array_get_size(v_last_735_);
v_newTailOff_739_ = lean_nat_sub(v_newSize_737_, v___x_738_);
v___x_754_ = lean_array_get_size(v_snd_730_);
v___x_755_ = lean_nat_dec_eq(v___x_754_, v___x_736_);
if (v___x_755_ == 0)
{
v___y_741_ = v___x_755_;
goto v___jp_740_;
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_array_fget_borrowed(v_snd_730_, v___x_722_);
v___x_757_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_756_);
v___y_741_ = v___x_757_;
goto v___jp_740_;
}
v___jp_740_:
{
if (v___y_741_ == 0)
{
lean_object* v___x_743_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v_snd_730_);
v___x_743_ = v___x_733_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_snd_730_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v_newTailOff_739_);
lean_ctor_set(v___x_728_, 2, v_newSize_737_);
lean_ctor_set(v___x_728_, 1, v_last_735_);
lean_ctor_set(v___x_728_, 0, v___x_743_);
v___x_745_ = v___x_728_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_last_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_newSize_737_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_newTailOff_739_);
lean_ctor_set_usize(v_reuseFailAlloc_746_, 4, v_shift_720_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v___x_748_; size_t v___x_749_; size_t v___x_750_; lean_object* v___x_752_; 
lean_del_object(v___x_733_);
v___x_748_ = lean_array_fget(v_snd_730_, v___x_722_);
lean_dec(v_snd_730_);
v___x_749_ = ((size_t)5ULL);
v___x_750_ = lean_usize_sub(v_shift_720_, v___x_749_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v_newTailOff_739_);
lean_ctor_set(v___x_728_, 2, v_newSize_737_);
lean_ctor_set(v___x_728_, 1, v_last_735_);
lean_ctor_set(v___x_728_, 0, v___x_748_);
v___x_752_ = v___x_728_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_last_735_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_newSize_737_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_newTailOff_739_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_ctor_set_usize(v___x_752_, 4, v___x_750_);
return v___x_752_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_773_; 
lean_inc(v_tailOff_721_);
lean_inc(v_size_719_);
lean_inc_ref(v_tail_718_);
lean_inc_ref(v_root_717_);
v_isSharedCheck_773_ = !lean_is_exclusive(v_t_716_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_774_ = lean_ctor_get(v_t_716_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_t_716_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_t_716_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_t_716_, 0);
lean_dec(v_unused_777_);
v___x_765_ = v_t_716_;
v_isShared_766_ = v_isSharedCheck_773_;
goto v_resetjp_764_;
}
else
{
lean_dec(v_t_716_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_773_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_767_ = lean_array_pop(v_tail_718_);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_sub(v_size_719_, v___x_768_);
lean_dec(v_size_719_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 2, v___x_769_);
lean_ctor_set(v___x_765_, 1, v___x_767_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_root_717_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_tailOff_721_);
lean_ctor_set_usize(v_reuseFailAlloc_772_, 4, v_shift_720_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_778_, lean_object* v_t_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentArray_pop___redArg(v_t_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_781_, lean_object* v_f_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v_toApplicative_785_; lean_object* v_cs_786_; lean_object* v_toPure_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_781_, 0);
v_cs_786_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_cs_786_);
lean_dec_ref_known(v_x_783_, 1);
v_toPure_787_ = lean_ctor_get(v_toApplicative_785_, 1);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_array_get_size(v_cs_786_);
v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_inc(v_toPure_787_);
lean_dec_ref(v_cs_786_);
lean_dec(v_f_782_);
lean_dec_ref(v_inst_781_);
v___x_791_ = lean_apply_2(v_toPure_787_, lean_box(0), v_x_784_);
return v___x_791_;
}
else
{
lean_object* v___f_792_; uint8_t v___x_793_; 
lean_inc_ref(v_inst_781_);
v___f_792_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_792_, 0, v_inst_781_);
lean_closure_set(v___f_792_, 1, v_f_782_);
v___x_793_ = lean_nat_dec_le(v___x_789_, v___x_789_);
if (v___x_793_ == 0)
{
if (v___x_790_ == 0)
{
lean_object* v___x_794_; 
lean_inc(v_toPure_787_);
lean_dec_ref(v___f_792_);
lean_dec_ref(v_cs_786_);
lean_dec_ref(v_inst_781_);
v___x_794_ = lean_apply_2(v_toPure_787_, lean_box(0), v_x_784_);
return v___x_794_;
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_of_nat(v___x_789_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v___f_792_, v_cs_786_, v___x_795_, v___x_796_, v_x_784_);
return v___x_797_;
}
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_789_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v___f_792_, v_cs_786_, v___x_798_, v___x_799_, v_x_784_);
return v___x_800_;
}
}
}
else
{
lean_object* v_toApplicative_801_; lean_object* v_vs_802_; lean_object* v_toPure_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_toApplicative_801_ = lean_ctor_get(v_inst_781_, 0);
v_vs_802_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_vs_802_);
lean_dec_ref_known(v_x_783_, 1);
v_toPure_803_ = lean_ctor_get(v_toApplicative_801_, 1);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v_vs_802_);
v___x_806_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_inc(v_toPure_803_);
lean_dec_ref(v_vs_802_);
lean_dec(v_f_782_);
lean_dec_ref(v_inst_781_);
v___x_807_ = lean_apply_2(v_toPure_803_, lean_box(0), v_x_784_);
return v___x_807_;
}
else
{
uint8_t v___x_808_; 
v___x_808_ = lean_nat_dec_le(v___x_805_, v___x_805_);
if (v___x_808_ == 0)
{
if (v___x_806_ == 0)
{
lean_object* v___x_809_; 
lean_inc(v_toPure_803_);
lean_dec_ref(v_vs_802_);
lean_dec(v_f_782_);
lean_dec_ref(v_inst_781_);
v___x_809_ = lean_apply_2(v_toPure_803_, lean_box(0), v_x_784_);
return v___x_809_;
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_805_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v_f_782_, v_vs_802_, v___x_810_, v___x_811_, v_x_784_);
return v___x_812_;
}
}
else
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_805_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v_f_782_, v_vs_802_, v___x_813_, v___x_814_, v_x_784_);
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_816_, lean_object* v_f_817_, lean_object* v_b_818_, lean_object* v_c_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_816_, v_f_817_, v_c_819_, v_b_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_821_, lean_object* v_m_822_, lean_object* v_inst_823_, lean_object* v_00_u03b2_824_, lean_object* v_f_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_823_, v_f_825_, v_x_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_toApplicative_829_, lean_object* v_j_830_, lean_object* v_cs_831_, lean_object* v_inst_832_, lean_object* v___f_833_, lean_object* v_b_834_){
_start:
{
lean_object* v_toPure_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_toPure_835_ = lean_ctor_get(v_toApplicative_829_, 1);
lean_inc(v_toPure_835_);
lean_dec_ref(v_toApplicative_829_);
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_j_830_, v___x_836_);
v___x_838_ = lean_array_get_size(v_cs_831_);
v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_dec(v___x_837_);
lean_dec(v___f_833_);
lean_dec_ref(v_inst_832_);
lean_dec_ref(v_cs_831_);
v___x_840_ = lean_apply_2(v_toPure_835_, lean_box(0), v_b_834_);
return v___x_840_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_le(v___x_838_, v___x_838_);
if (v___x_841_ == 0)
{
if (v___x_839_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v___x_837_);
lean_dec(v___f_833_);
lean_dec_ref(v_inst_832_);
lean_dec_ref(v_cs_831_);
v___x_842_ = lean_apply_2(v_toPure_835_, lean_box(0), v_b_834_);
return v___x_842_;
}
else
{
size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
lean_dec(v_toPure_835_);
v___x_843_ = lean_usize_of_nat(v___x_837_);
lean_dec(v___x_837_);
v___x_844_ = lean_usize_of_nat(v___x_838_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v___f_833_, v_cs_831_, v___x_843_, v___x_844_, v_b_834_);
return v___x_845_;
}
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
lean_dec(v_toPure_835_);
v___x_846_ = lean_usize_of_nat(v___x_837_);
lean_dec(v___x_837_);
v___x_847_ = lean_usize_of_nat(v___x_838_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v___f_833_, v_cs_831_, v___x_846_, v___x_847_, v_b_834_);
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_849_, lean_object* v_j_850_, lean_object* v_cs_851_, lean_object* v_inst_852_, lean_object* v___f_853_, lean_object* v_b_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_toApplicative_849_, v_j_850_, v_cs_851_, v_inst_852_, v___f_853_, v_b_854_);
lean_dec(v_j_850_);
return v_res_855_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_856_, lean_object* v_f_857_, lean_object* v_x_858_, size_t v_x_859_, size_t v_x_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_858_) == 0)
{
lean_object* v_toApplicative_862_; lean_object* v_toBind_863_; lean_object* v_cs_864_; lean_object* v___f_865_; lean_object* v___x_866_; size_t v___x_867_; lean_object* v_j_868_; lean_object* v___f_869_; lean_object* v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_toApplicative_862_ = lean_ctor_get(v_inst_856_, 0);
v_toBind_863_ = lean_ctor_get(v_inst_856_, 1);
lean_inc(v_toBind_863_);
v_cs_864_ = lean_ctor_get(v_x_858_, 0);
lean_inc_ref_n(v_cs_864_, 2);
lean_dec_ref_known(v_x_858_, 1);
lean_inc(v_f_857_);
lean_inc_ref_n(v_inst_856_, 2);
v___f_865_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_865_, 0, v_inst_856_);
lean_closure_set(v___f_865_, 1, v_f_857_);
v___x_866_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_867_ = lean_usize_shift_right(v_x_859_, v_x_860_);
v_j_868_ = lean_usize_to_nat(v___x_867_);
lean_inc(v_j_868_);
lean_inc_ref(v_toApplicative_862_);
v___f_869_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_869_, 0, v_toApplicative_862_);
lean_closure_set(v___f_869_, 1, v_j_868_);
lean_closure_set(v___f_869_, 2, v_cs_864_);
lean_closure_set(v___f_869_, 3, v_inst_856_);
lean_closure_set(v___f_869_, 4, v___f_865_);
v___x_870_ = lean_array_get(v___x_866_, v_cs_864_, v_j_868_);
lean_dec(v_j_868_);
lean_dec_ref(v_cs_864_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_shift_left(v___x_871_, v_x_860_);
v___x_873_ = lean_usize_sub(v___x_872_, v___x_871_);
v___x_874_ = lean_usize_land(v_x_859_, v___x_873_);
v___x_875_ = ((size_t)5ULL);
v___x_876_ = lean_usize_sub(v_x_860_, v___x_875_);
v___x_877_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_856_, v_f_857_, v___x_870_, v___x_874_, v___x_876_, v_x_861_);
v___x_878_ = lean_apply_4(v_toBind_863_, lean_box(0), lean_box(0), v___x_877_, v___f_869_);
return v___x_878_;
}
else
{
lean_object* v_toApplicative_879_; lean_object* v_vs_880_; lean_object* v_toPure_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_toApplicative_879_ = lean_ctor_get(v_inst_856_, 0);
v_vs_880_ = lean_ctor_get(v_x_858_, 0);
lean_inc_ref(v_vs_880_);
lean_dec_ref_known(v_x_858_, 1);
v_toPure_881_ = lean_ctor_get(v_toApplicative_879_, 1);
v___x_882_ = lean_usize_to_nat(v_x_859_);
v___x_883_ = lean_array_get_size(v_vs_880_);
v___x_884_ = lean_nat_dec_lt(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_inc(v_toPure_881_);
lean_dec(v___x_882_);
lean_dec_ref(v_vs_880_);
lean_dec(v_f_857_);
lean_dec_ref(v_inst_856_);
v___x_885_ = lean_apply_2(v_toPure_881_, lean_box(0), v_x_861_);
return v___x_885_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = lean_nat_dec_le(v___x_883_, v___x_883_);
if (v___x_886_ == 0)
{
if (v___x_884_ == 0)
{
lean_object* v___x_887_; 
lean_inc(v_toPure_881_);
lean_dec(v___x_882_);
lean_dec_ref(v_vs_880_);
lean_dec(v_f_857_);
lean_dec_ref(v_inst_856_);
v___x_887_ = lean_apply_2(v_toPure_881_, lean_box(0), v_x_861_);
return v___x_887_;
}
else
{
size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_usize_of_nat(v___x_882_);
lean_dec(v___x_882_);
v___x_889_ = lean_usize_of_nat(v___x_883_);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_856_, v_f_857_, v_vs_880_, v___x_888_, v___x_889_, v_x_861_);
return v___x_890_;
}
}
else
{
size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_usize_of_nat(v___x_882_);
lean_dec(v___x_882_);
v___x_892_ = lean_usize_of_nat(v___x_883_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_856_, v_f_857_, v_vs_880_, v___x_891_, v___x_892_, v_x_861_);
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_856_ = stack[0].m_obj;
lean_object* v_f_857_ = stack[1].m_obj;
lean_object* v_x_858_ = stack[2].m_obj;
size_t v_x_859_ = stack[3].m_num;
size_t v_x_860_ = stack[4].m_num;
lean_object* v_x_861_ = stack[5].m_obj;
lean_object* v_res_894_;
v_res_894_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_856_, v_f_857_, v_x_858_, v_x_859_, v_x_860_, v_x_861_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_895_, lean_object* v_f_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
size_t v_x_226__boxed_901_; size_t v_x_227__boxed_902_; lean_object* v_res_903_; 
v_x_226__boxed_901_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_x_227__boxed_902_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_903_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_895_, v_f_896_, v_x_897_, v_x_226__boxed_901_, v_x_227__boxed_902_, v_x_900_);
return v_res_903_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_904_, lean_object* v_m_905_, lean_object* v_inst_906_, lean_object* v_00_u03b2_907_, lean_object* v_f_908_, lean_object* v_x_909_, size_t v_x_910_, size_t v_x_911_, lean_object* v_x_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_906_, v_f_908_, v_x_909_, v_x_910_, v_x_911_, v_x_912_);
return v___x_913_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_906_ = stack[2].m_obj;
lean_object* v_f_908_ = stack[4].m_obj;
lean_object* v_x_909_ = stack[5].m_obj;
size_t v_x_910_ = stack[6].m_num;
size_t v_x_911_ = stack[7].m_num;
lean_object* v_x_912_ = stack[8].m_obj;
lean_object* v_res_914_;
v_res_914_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_box(0), lean_box(0), v_inst_906_, lean_box(0), v_f_908_, v_x_909_, v_x_910_, v_x_911_, v_x_912_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_915_, lean_object* v_m_916_, lean_object* v_inst_917_, lean_object* v_00_u03b2_918_, lean_object* v_f_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
size_t v_x_332__boxed_924_; size_t v_x_333__boxed_925_; lean_object* v_res_926_; 
v_x_332__boxed_924_ = lean_unbox_usize(v_x_921_);
lean_dec(v_x_921_);
v_x_333__boxed_925_ = lean_unbox_usize(v_x_922_);
lean_dec(v_x_922_);
v_res_926_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_915_, v_m_916_, v_inst_917_, v_00_u03b2_918_, v_f_919_, v_x_920_, v_x_332__boxed_924_, v_x_333__boxed_925_, v_x_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_toApplicative_927_, lean_object* v_tail_928_, lean_object* v___x_929_, lean_object* v_inst_930_, lean_object* v_f_931_, lean_object* v_b_932_){
_start:
{
lean_object* v_toPure_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_toPure_933_ = lean_ctor_get(v_toApplicative_927_, 1);
lean_inc(v_toPure_933_);
lean_dec_ref(v_toApplicative_927_);
v___x_934_ = lean_array_get_size(v_tail_928_);
v___x_935_ = lean_nat_dec_lt(v___x_929_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec(v_f_931_);
lean_dec_ref(v_inst_930_);
lean_dec_ref(v_tail_928_);
v___x_936_ = lean_apply_2(v_toPure_933_, lean_box(0), v_b_932_);
return v___x_936_;
}
else
{
uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_le(v___x_934_, v___x_934_);
if (v___x_937_ == 0)
{
if (v___x_935_ == 0)
{
lean_object* v___x_938_; 
lean_dec(v_f_931_);
lean_dec_ref(v_inst_930_);
lean_dec_ref(v_tail_928_);
v___x_938_ = lean_apply_2(v_toPure_933_, lean_box(0), v_b_932_);
return v___x_938_;
}
else
{
size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; 
lean_dec(v_toPure_933_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = lean_usize_of_nat(v___x_934_);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_930_, v_f_931_, v_tail_928_, v___x_939_, v___x_940_, v_b_932_);
return v___x_941_;
}
}
else
{
size_t v___x_942_; size_t v___x_943_; lean_object* v___x_944_; 
lean_dec(v_toPure_933_);
v___x_942_ = ((size_t)0ULL);
v___x_943_ = lean_usize_of_nat(v___x_934_);
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_930_, v_f_931_, v_tail_928_, v___x_942_, v___x_943_, v_b_932_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_toApplicative_945_, lean_object* v_tail_946_, lean_object* v___x_947_, lean_object* v_inst_948_, lean_object* v_f_949_, lean_object* v_b_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_toApplicative_945_, v_tail_946_, v___x_947_, v_inst_948_, v_f_949_, v_b_950_);
lean_dec(v___x_947_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_952_, lean_object* v_t_953_, lean_object* v_f_954_, lean_object* v_init_955_, lean_object* v_start_956_){
_start:
{
lean_object* v_toApplicative_957_; lean_object* v_toBind_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_toApplicative_957_ = lean_ctor_get(v_inst_952_, 0);
v_toBind_958_ = lean_ctor_get(v_inst_952_, 1);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_nat_dec_eq(v_start_956_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v_root_961_; lean_object* v_tail_962_; size_t v_shift_963_; lean_object* v_tailOff_964_; uint8_t v___x_965_; 
v_root_961_ = lean_ctor_get(v_t_953_, 0);
lean_inc_ref(v_root_961_);
v_tail_962_ = lean_ctor_get(v_t_953_, 1);
lean_inc_ref(v_tail_962_);
v_shift_963_ = lean_ctor_get_usize(v_t_953_, 4);
v_tailOff_964_ = lean_ctor_get(v_t_953_, 3);
lean_inc(v_tailOff_964_);
lean_dec_ref(v_t_953_);
v___x_965_ = lean_nat_dec_le(v_tailOff_964_, v_start_956_);
if (v___x_965_ == 0)
{
lean_object* v___f_966_; size_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc(v_toBind_958_);
lean_dec(v_tailOff_964_);
lean_inc(v_f_954_);
lean_inc_ref(v_inst_952_);
lean_inc_ref(v_toApplicative_957_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_966_, 0, v_toApplicative_957_);
lean_closure_set(v___f_966_, 1, v_tail_962_);
lean_closure_set(v___f_966_, 2, v___x_959_);
lean_closure_set(v___f_966_, 3, v_inst_952_);
lean_closure_set(v___f_966_, 4, v_f_954_);
v___x_967_ = lean_usize_of_nat(v_start_956_);
v___x_968_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_952_, v_f_954_, v_root_961_, v___x_967_, v_shift_963_, v_init_955_);
v___x_969_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___x_968_, v___f_966_);
return v___x_969_;
}
else
{
lean_object* v_toPure_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
lean_dec_ref(v_root_961_);
v_toPure_970_ = lean_ctor_get(v_toApplicative_957_, 1);
v___x_971_ = lean_nat_sub(v_start_956_, v_tailOff_964_);
lean_dec(v_tailOff_964_);
v___x_972_ = lean_array_get_size(v_tail_962_);
v___x_973_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_inc(v_toPure_970_);
lean_dec(v___x_971_);
lean_dec_ref(v_tail_962_);
lean_dec(v_f_954_);
lean_dec_ref(v_inst_952_);
v___x_974_ = lean_apply_2(v_toPure_970_, lean_box(0), v_init_955_);
return v___x_974_;
}
else
{
uint8_t v___x_975_; 
v___x_975_ = lean_nat_dec_le(v___x_972_, v___x_972_);
if (v___x_975_ == 0)
{
if (v___x_973_ == 0)
{
lean_object* v___x_976_; 
lean_inc(v_toPure_970_);
lean_dec(v___x_971_);
lean_dec_ref(v_tail_962_);
lean_dec(v_f_954_);
lean_dec_ref(v_inst_952_);
v___x_976_ = lean_apply_2(v_toPure_970_, lean_box(0), v_init_955_);
return v___x_976_;
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_usize_of_nat(v___x_971_);
lean_dec(v___x_971_);
v___x_978_ = lean_usize_of_nat(v___x_972_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_952_, v_f_954_, v_tail_962_, v___x_977_, v___x_978_, v_init_955_);
return v___x_979_;
}
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_usize_of_nat(v___x_971_);
lean_dec(v___x_971_);
v___x_981_ = lean_usize_of_nat(v___x_972_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_952_, v_f_954_, v_tail_962_, v___x_980_, v___x_981_, v_init_955_);
return v___x_982_;
}
}
}
}
else
{
lean_object* v_root_983_; lean_object* v_tail_984_; lean_object* v___f_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_inc(v_toBind_958_);
v_root_983_ = lean_ctor_get(v_t_953_, 0);
lean_inc_ref(v_root_983_);
v_tail_984_ = lean_ctor_get(v_t_953_, 1);
lean_inc_ref(v_tail_984_);
lean_dec_ref(v_t_953_);
lean_inc(v_f_954_);
lean_inc_ref(v_inst_952_);
lean_inc_ref(v_toApplicative_957_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_985_, 0, v_toApplicative_957_);
lean_closure_set(v___f_985_, 1, v_tail_984_);
lean_closure_set(v___f_985_, 2, v___x_959_);
lean_closure_set(v___f_985_, 3, v_inst_952_);
lean_closure_set(v___f_985_, 4, v_f_954_);
v___x_986_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_952_, v_f_954_, v_root_983_, v_init_955_);
v___x_987_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___x_986_, v___f_985_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_988_, lean_object* v_t_989_, lean_object* v_f_990_, lean_object* v_init_991_, lean_object* v_start_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_988_, v_t_989_, v_f_990_, v_init_991_, v_start_992_);
lean_dec(v_start_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_994_, lean_object* v_m_995_, lean_object* v_inst_996_, lean_object* v_00_u03b2_997_, lean_object* v_t_998_, lean_object* v_f_999_, lean_object* v_init_1000_, lean_object* v_start_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_996_, v_t_998_, v_f_999_, v_init_1000_, v_start_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_m_1004_, lean_object* v_inst_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_t_1007_, lean_object* v_f_1008_, lean_object* v_init_1009_, lean_object* v_start_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_1003_, v_m_1004_, v_inst_1005_, v_00_u03b2_1006_, v_t_1007_, v_f_1008_, v_init_1009_, v_start_1010_);
lean_dec(v_start_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_1012_, lean_object* v_f_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v_toApplicative_1016_; lean_object* v_cs_1017_; lean_object* v_toPure_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_toApplicative_1016_ = lean_ctor_get(v_inst_1012_, 0);
v_cs_1017_ = lean_ctor_get(v_x_1014_, 0);
lean_inc_ref(v_cs_1017_);
lean_dec_ref_known(v_x_1014_, 1);
v_toPure_1018_ = lean_ctor_get(v_toApplicative_1016_, 1);
v___x_1019_ = lean_array_get_size(v_cs_1017_);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_nat_dec_lt(v___x_1020_, v___x_1019_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
lean_inc(v_toPure_1018_);
lean_dec_ref(v_cs_1017_);
lean_dec(v_f_1013_);
lean_dec_ref(v_inst_1012_);
v___x_1022_ = lean_apply_2(v_toPure_1018_, lean_box(0), v_x_1015_);
return v___x_1022_;
}
else
{
lean_object* v___f_1023_; size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
lean_inc_ref(v_inst_1012_);
v___f_1023_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1023_, 0, v_inst_1012_);
lean_closure_set(v___f_1023_, 1, v_f_1013_);
v___x_1024_ = lean_usize_of_nat(v___x_1019_);
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1012_, v___f_1023_, v_cs_1017_, v___x_1024_, v___x_1025_, v_x_1015_);
return v___x_1026_;
}
}
else
{
lean_object* v_toApplicative_1027_; lean_object* v_vs_1028_; lean_object* v_toPure_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_toApplicative_1027_ = lean_ctor_get(v_inst_1012_, 0);
v_vs_1028_ = lean_ctor_get(v_x_1014_, 0);
lean_inc_ref(v_vs_1028_);
lean_dec_ref_known(v_x_1014_, 1);
v_toPure_1029_ = lean_ctor_get(v_toApplicative_1027_, 1);
v___x_1030_ = lean_array_get_size(v_vs_1028_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_nat_dec_lt(v___x_1031_, v___x_1030_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_inc(v_toPure_1029_);
lean_dec_ref(v_vs_1028_);
lean_dec(v_f_1013_);
lean_dec_ref(v_inst_1012_);
v___x_1033_ = lean_apply_2(v_toPure_1029_, lean_box(0), v_x_1015_);
return v___x_1033_;
}
else
{
size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_usize_of_nat(v___x_1030_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1012_, v_f_1013_, v_vs_1028_, v___x_1034_, v___x_1035_, v_x_1015_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_1037_, lean_object* v_f_1038_, lean_object* v_c_1039_, lean_object* v_b_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1037_, v_f_1038_, v_c_1039_, v_b_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_1042_, lean_object* v_m_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_inst_1045_, lean_object* v_f_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1045_, v_f_1046_, v_x_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_1050_, lean_object* v_f_1051_, lean_object* v_root_1052_, lean_object* v_____do__lift_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1050_, v_f_1051_, v_root_1052_, v_____do__lift_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1055_, lean_object* v_t_1056_, lean_object* v_f_1057_, lean_object* v_init_1058_){
_start:
{
lean_object* v_toApplicative_1059_; lean_object* v_toBind_1060_; lean_object* v_root_1061_; lean_object* v_tail_1062_; lean_object* v_toPure_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_toApplicative_1059_ = lean_ctor_get(v_inst_1055_, 0);
v_toBind_1060_ = lean_ctor_get(v_inst_1055_, 1);
lean_inc(v_toBind_1060_);
v_root_1061_ = lean_ctor_get(v_t_1056_, 0);
lean_inc_ref(v_root_1061_);
v_tail_1062_ = lean_ctor_get(v_t_1056_, 1);
lean_inc_ref(v_tail_1062_);
lean_dec_ref(v_t_1056_);
v_toPure_1063_ = lean_ctor_get(v_toApplicative_1059_, 1);
lean_inc(v_f_1057_);
lean_inc_ref(v_inst_1055_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1064_, 0, v_inst_1055_);
lean_closure_set(v___f_1064_, 1, v_f_1057_);
lean_closure_set(v___f_1064_, 2, v_root_1061_);
v___x_1065_ = lean_array_get_size(v_tail_1062_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_nat_dec_lt(v___x_1066_, v___x_1065_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_inc(v_toPure_1063_);
lean_dec_ref(v_tail_1062_);
lean_dec(v_f_1057_);
lean_dec_ref(v_inst_1055_);
v___x_1068_ = lean_apply_2(v_toPure_1063_, lean_box(0), v_init_1058_);
v___x_1069_ = lean_apply_4(v_toBind_1060_, lean_box(0), lean_box(0), v___x_1068_, v___f_1064_);
return v___x_1069_;
}
else
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = lean_usize_of_nat(v___x_1065_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1055_, v_f_1057_, v_tail_1062_, v___x_1070_, v___x_1071_, v_init_1058_);
v___x_1073_ = lean_apply_4(v_toBind_1060_, lean_box(0), lean_box(0), v___x_1072_, v___f_1064_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1074_, lean_object* v_m_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_inst_1077_, lean_object* v_t_1078_, lean_object* v_f_1079_, lean_object* v_init_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1077_, v_t_1078_, v_f_1079_, v_init_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1082_, lean_object* v_____s_1083_){
_start:
{
lean_object* v_fst_1084_; 
v_fst_1084_ = lean_ctor_get(v_____s_1083_, 0);
if (lean_obj_tag(v_fst_1084_) == 0)
{
lean_object* v_snd_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_snd_1085_ = lean_ctor_get(v_____s_1083_, 1);
lean_inc(v_snd_1085_);
lean_dec_ref(v_____s_1083_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_snd_1085_);
v___x_1087_ = lean_apply_2(v_toPure_1082_, lean_box(0), v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
lean_inc_ref(v_fst_1084_);
lean_dec_ref(v_____s_1083_);
v_val_1088_ = lean_ctor_get(v_fst_1084_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_fst_1084_, 1);
v___x_1089_ = lean_apply_2(v_toPure_1082_, lean_box(0), v_val_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1090_, lean_object* v_toPure_1091_, lean_object* v___x_1092_, lean_object* v_____do__lift_1093_){
_start:
{
if (lean_obj_tag(v_____do__lift_1093_) == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v___x_1092_);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_____do__lift_1093_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_snd_1090_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v___x_1097_ = lean_apply_2(v_toPure_1091_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_snd_1090_);
v_a_1098_ = lean_ctor_get(v_____do__lift_1093_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_____do__lift_1093_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1100_ = v_____do__lift_1093_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v_____do__lift_1093_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1092_);
lean_ctor_set(v___x_1102_, 1, v_a_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_apply_2(v_toPure_1091_, lean_box(0), v___x_1104_);
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1108_, lean_object* v___x_1109_, lean_object* v_f_1110_, lean_object* v_toBind_1111_, lean_object* v_a_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_snd_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_snd_1115_ = lean_ctor_get(v___y_1114_, 1);
lean_inc_n(v_snd_1115_, 2);
lean_dec_ref(v___y_1114_);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1116_, 0, v_snd_1115_);
lean_closure_set(v___f_1116_, 1, v_toPure_1108_);
lean_closure_set(v___f_1116_, 2, v___x_1109_);
v___x_1117_ = lean_apply_2(v_f_1110_, v_a_1112_, v_snd_1115_);
v___x_1118_ = lean_apply_4(v_toBind_1111_, lean_box(0), lean_box(0), v___x_1117_, v___f_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1119_, lean_object* v___x_1120_, lean_object* v_inst_1121_, lean_object* v_f_1122_, lean_object* v_toBind_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1119_, v___x_1120_, v_inst_1121_, v_f_1122_, v_toBind_1123_, v_a_1124_, v_x_1125_, v___y_1126_);
lean_dec_ref(v_a_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1128_, lean_object* v_f_1129_, lean_object* v_n_1130_, lean_object* v_b_1131_){
_start:
{
if (lean_obj_tag(v_n_1130_) == 0)
{
lean_object* v_toApplicative_1132_; lean_object* v_toBind_1133_; lean_object* v_toPure_1134_; lean_object* v_cs_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_toApplicative_1132_ = lean_ctor_get(v_inst_1128_, 0);
v_toBind_1133_ = lean_ctor_get(v_inst_1128_, 1);
lean_inc_n(v_toBind_1133_, 2);
v_toPure_1134_ = lean_ctor_get(v_toApplicative_1132_, 1);
v_cs_1135_ = lean_ctor_get(v_n_1130_, 0);
lean_inc_n(v_toPure_1134_, 2);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1136_, 0, v_toPure_1134_);
v___x_1137_ = lean_box(0);
lean_inc_ref(v_inst_1128_);
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1138_, 0, v_toPure_1134_);
lean_closure_set(v___f_1138_, 1, v___x_1137_);
lean_closure_set(v___f_1138_, 2, v_inst_1128_);
lean_closure_set(v___f_1138_, 3, v_f_1129_);
lean_closure_set(v___f_1138_, 4, v_toBind_1133_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v_b_1131_);
v_sz_1140_ = lean_array_size(v_cs_1135_);
v___x_1141_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1135_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1128_, v_cs_1135_, v___f_1138_, v_sz_1140_, v___x_1141_, v___x_1139_);
v___x_1143_ = lean_apply_4(v_toBind_1133_, lean_box(0), lean_box(0), v___x_1142_, v___f_1136_);
return v___x_1143_;
}
else
{
lean_object* v_toApplicative_1144_; lean_object* v_toBind_1145_; lean_object* v_toPure_1146_; lean_object* v_vs_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; size_t v_sz_1152_; size_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_toApplicative_1144_ = lean_ctor_get(v_inst_1128_, 0);
v_toBind_1145_ = lean_ctor_get(v_inst_1128_, 1);
lean_inc_n(v_toBind_1145_, 2);
v_toPure_1146_ = lean_ctor_get(v_toApplicative_1144_, 1);
v_vs_1147_ = lean_ctor_get(v_n_1130_, 0);
lean_inc_n(v_toPure_1146_, 2);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1148_, 0, v_toPure_1146_);
v___x_1149_ = lean_box(0);
v___f_1150_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1150_, 0, v_toPure_1146_);
lean_closure_set(v___f_1150_, 1, v___x_1149_);
lean_closure_set(v___f_1150_, 2, v_f_1129_);
lean_closure_set(v___f_1150_, 3, v_toBind_1145_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v_b_1131_);
v_sz_1152_ = lean_array_size(v_vs_1147_);
v___x_1153_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1147_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1128_, v_vs_1147_, v___f_1150_, v_sz_1152_, v___x_1153_, v___x_1151_);
v___x_1155_ = lean_apply_4(v_toBind_1145_, lean_box(0), lean_box(0), v___x_1154_, v___f_1148_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1156_, lean_object* v___x_1157_, lean_object* v_inst_1158_, lean_object* v_f_1159_, lean_object* v_toBind_1160_, lean_object* v_a_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_snd_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_snd_1164_ = lean_ctor_get(v___y_1163_, 1);
lean_inc_n(v_snd_1164_, 2);
lean_dec_ref(v___y_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1165_, 0, v_snd_1164_);
lean_closure_set(v___f_1165_, 1, v_toPure_1156_);
lean_closure_set(v___f_1165_, 2, v___x_1157_);
v___x_1166_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1158_, v_f_1159_, v_a_1161_, v_snd_1164_);
v___x_1167_ = lean_apply_4(v_toBind_1160_, lean_box(0), lean_box(0), v___x_1166_, v___f_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1168_, lean_object* v_f_1169_, lean_object* v_n_1170_, lean_object* v_b_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1168_, v_f_1169_, v_n_1170_, v_b_1171_);
lean_dec_ref(v_n_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_m_1175_, lean_object* v_inst_1176_, lean_object* v_inh_1177_, lean_object* v_f_1178_, lean_object* v_n_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1176_, v_f_1178_, v_n_1179_, v_b_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_m_1184_, lean_object* v_inst_1185_, lean_object* v_inh_1186_, lean_object* v_f_1187_, lean_object* v_n_1188_, lean_object* v_b_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1182_, v_00_u03b2_1183_, v_m_1184_, v_inst_1185_, v_inh_1186_, v_f_1187_, v_n_1188_, v_b_1189_);
lean_dec_ref(v_n_1188_);
lean_dec(v_inh_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1191_, lean_object* v_____s_1192_){
_start:
{
lean_object* v_fst_1193_; 
v_fst_1193_ = lean_ctor_get(v_____s_1192_, 0);
if (lean_obj_tag(v_fst_1193_) == 0)
{
lean_object* v_snd_1194_; lean_object* v___x_1195_; 
v_snd_1194_ = lean_ctor_get(v_____s_1192_, 1);
lean_inc(v_snd_1194_);
lean_dec_ref(v_____s_1192_);
v___x_1195_ = lean_apply_2(v_toPure_1191_, lean_box(0), v_snd_1194_);
return v___x_1195_;
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
lean_inc_ref(v_fst_1193_);
lean_dec_ref(v_____s_1192_);
v_val_1196_ = lean_ctor_get(v_fst_1193_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v_fst_1193_, 1);
v___x_1197_ = lean_apply_2(v_toPure_1191_, lean_box(0), v_val_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1198_, lean_object* v_toPure_1199_, lean_object* v___x_1200_, lean_object* v_____do__lift_1201_){
_start:
{
if (lean_obj_tag(v_____do__lift_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v___x_1200_);
v_a_1202_ = lean_ctor_get(v_____do__lift_1201_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_____do__lift_1201_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v_____do__lift_1201_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v_____do__lift_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_a_1202_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v_snd_1198_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_apply_2(v_toPure_1199_, lean_box(0), v___x_1209_);
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_snd_1198_);
v_a_1213_ = lean_ctor_get(v_____do__lift_1201_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_____do__lift_1201_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1215_ = v_____do__lift_1201_;
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v_____do__lift_1201_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1200_);
lean_ctor_set(v___x_1217_, 1, v_a_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_apply_2(v_toPure_1199_, lean_box(0), v___x_1219_);
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1223_, lean_object* v___x_1224_, lean_object* v_f_1225_, lean_object* v_toBind_1226_, lean_object* v_a_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_snd_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_snd_1230_ = lean_ctor_get(v___y_1229_, 1);
lean_inc_n(v_snd_1230_, 2);
lean_dec_ref(v___y_1229_);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1231_, 0, v_snd_1230_);
lean_closure_set(v___f_1231_, 1, v_toPure_1223_);
lean_closure_set(v___f_1231_, 2, v___x_1224_);
v___x_1232_ = lean_apply_2(v_f_1225_, v_a_1227_, v_snd_1230_);
v___x_1233_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v___x_1232_, v___f_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1234_, lean_object* v_f_1235_, lean_object* v_toBind_1236_, lean_object* v_tail_1237_, lean_object* v_inst_1238_, lean_object* v___f_1239_, lean_object* v_____do__lift_1240_){
_start:
{
if (lean_obj_tag(v_____do__lift_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; 
lean_dec(v___f_1239_);
lean_dec_ref(v_inst_1238_);
lean_dec_ref(v_tail_1237_);
lean_dec(v_toBind_1236_);
lean_dec(v_f_1235_);
v_a_1241_ = lean_ctor_get(v_____do__lift_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v_____do__lift_1240_, 1);
v___x_1242_ = lean_apply_2(v_toPure_1234_, lean_box(0), v_a_1241_);
return v___x_1242_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; size_t v_sz_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1243_ = lean_ctor_get(v_____do__lift_1240_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v_____do__lift_1240_, 1);
v___x_1244_ = lean_box(0);
lean_inc(v_toBind_1236_);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1245_, 0, v_toPure_1234_);
lean_closure_set(v___f_1245_, 1, v___x_1244_);
lean_closure_set(v___f_1245_, 2, v_f_1235_);
lean_closure_set(v___f_1245_, 3, v_toBind_1236_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v_a_1243_);
v_sz_1247_ = lean_array_size(v_tail_1237_);
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v_tail_1237_, v___f_1245_, v_sz_1247_, v___x_1248_, v___x_1246_);
v___x_1250_ = lean_apply_4(v_toBind_1236_, lean_box(0), lean_box(0), v___x_1249_, v___f_1239_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1251_, lean_object* v_t_1252_, lean_object* v_init_1253_, lean_object* v_f_1254_){
_start:
{
lean_object* v_toApplicative_1255_; lean_object* v_toBind_1256_; lean_object* v_root_1257_; lean_object* v_tail_1258_; lean_object* v_toPure_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; 
v_toApplicative_1255_ = lean_ctor_get(v_inst_1251_, 0);
v_toBind_1256_ = lean_ctor_get(v_inst_1251_, 1);
lean_inc_n(v_toBind_1256_, 2);
v_root_1257_ = lean_ctor_get(v_t_1252_, 0);
v_tail_1258_ = lean_ctor_get(v_t_1252_, 1);
v_toPure_1259_ = lean_ctor_get(v_toApplicative_1255_, 1);
lean_inc_n(v_toPure_1259_, 2);
lean_inc(v_f_1254_);
lean_inc_ref(v_inst_1251_);
v___x_1260_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1251_, v_f_1254_, v_root_1257_, v_init_1253_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1261_, 0, v_toPure_1259_);
lean_inc_ref(v_tail_1258_);
v___f_1262_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1262_, 0, v_toPure_1259_);
lean_closure_set(v___f_1262_, 1, v_f_1254_);
lean_closure_set(v___f_1262_, 2, v_toBind_1256_);
lean_closure_set(v___f_1262_, 3, v_tail_1258_);
lean_closure_set(v___f_1262_, 4, v_inst_1251_);
lean_closure_set(v___f_1262_, 5, v___f_1261_);
v___x_1263_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v___x_1260_, v___f_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1264_, lean_object* v_t_1265_, lean_object* v_init_1266_, lean_object* v_f_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1264_, v_t_1265_, v_init_1266_, v_f_1267_);
lean_dec_ref(v_t_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1269_, lean_object* v_m_1270_, lean_object* v_inst_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_t_1273_, lean_object* v_init_1274_, lean_object* v_f_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1271_, v_t_1273_, v_init_1274_, v_f_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_m_1278_, lean_object* v_inst_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_t_1281_, lean_object* v_init_1282_, lean_object* v_f_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1277_, v_m_1278_, v_inst_1279_, v_00_u03b2_1280_, v_t_1281_, v_init_1282_, v_f_1283_);
lean_dec_ref(v_t_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1286_, 0, lean_box(0));
lean_closure_set(v___x_1286_, 1, lean_box(0));
lean_closure_set(v___x_1286_, 2, v_inst_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1287_, lean_object* v_m_1288_, lean_object* v_inst_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1290_, 0, lean_box(0));
lean_closure_set(v___x_1290_, 1, lean_box(0));
lean_closure_set(v___x_1290_, 2, v_inst_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1291_, lean_object* v_____s_1292_){
_start:
{
lean_object* v_fst_1293_; 
v_fst_1293_ = lean_ctor_get(v_____s_1292_, 0);
lean_inc(v_fst_1293_);
lean_dec_ref(v_____s_1292_);
if (lean_obj_tag(v_fst_1293_) == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_apply_2(v_toPure_1291_, lean_box(0), v___x_1294_);
return v___x_1295_;
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1297_; 
v_val_1296_ = lean_ctor_get(v_fst_1293_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_fst_1293_, 1);
v___x_1297_ = lean_apply_2(v_toPure_1291_, lean_box(0), v_val_1296_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1298_, lean_object* v_toPure_1299_, lean_object* v___x_1300_, lean_object* v_____do__lift_1301_){
_start:
{
if (lean_obj_tag(v_____do__lift_1301_) == 1)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v___x_1300_);
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_____do__lift_1301_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1298_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
v___x_1305_ = lean_apply_2(v_toPure_1299_, lean_box(0), v___x_1304_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v_____do__lift_1301_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1300_);
v___x_1307_ = lean_apply_2(v_toPure_1299_, lean_box(0), v___x_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1308_, lean_object* v_toBind_1309_, lean_object* v___f_1310_, lean_object* v_a_1311_, lean_object* v_x_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_apply_1(v_f_1308_, v_a_1311_);
v___x_1315_ = lean_apply_4(v_toBind_1309_, lean_box(0), lean_box(0), v___x_1314_, v___f_1310_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1316_, lean_object* v_toBind_1317_, lean_object* v___f_1318_, lean_object* v_a_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1316_, v_toBind_1317_, v___f_1318_, v_a_1319_, v_x_1320_, v___y_1321_);
lean_dec_ref(v___y_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1326_, lean_object* v_f_1327_, lean_object* v_toBind_1328_, lean_object* v___f_1329_, lean_object* v_a_1330_, lean_object* v_x_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1326_, v_f_1327_, v_toBind_1328_, v___f_1329_, v_a_1330_, v_x_1331_, v___y_1332_);
lean_dec_ref(v___y_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1334_, lean_object* v_f_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v_toApplicative_1337_; lean_object* v_cs_1338_; lean_object* v_toBind_1339_; lean_object* v_toPure_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___f_1345_; size_t v_sz_1346_; size_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_toApplicative_1337_ = lean_ctor_get(v_inst_1334_, 0);
v_cs_1338_ = lean_ctor_get(v_x_1336_, 0);
lean_inc_ref(v_cs_1338_);
lean_dec_ref_known(v_x_1336_, 1);
v_toBind_1339_ = lean_ctor_get(v_inst_1334_, 1);
lean_inc_n(v_toBind_1339_, 2);
v_toPure_1340_ = lean_ctor_get(v_toApplicative_1337_, 1);
v___x_1341_ = lean_box(0);
v___x_1342_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1340_, 2);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1343_, 0, v_toPure_1340_);
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1344_, 0, v___x_1341_);
lean_closure_set(v___f_1344_, 1, v_toPure_1340_);
lean_closure_set(v___f_1344_, 2, v___x_1342_);
lean_inc_ref(v_inst_1334_);
v___f_1345_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1345_, 0, v_inst_1334_);
lean_closure_set(v___f_1345_, 1, v_f_1335_);
lean_closure_set(v___f_1345_, 2, v_toBind_1339_);
lean_closure_set(v___f_1345_, 3, v___f_1344_);
v_sz_1346_ = lean_array_size(v_cs_1338_);
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1334_, v_cs_1338_, v___f_1345_, v_sz_1346_, v___x_1347_, v___x_1342_);
v___x_1349_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v___x_1348_, v___f_1343_);
return v___x_1349_;
}
else
{
lean_object* v_toApplicative_1350_; lean_object* v_vs_1351_; lean_object* v_toBind_1352_; lean_object* v_toPure_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; size_t v_sz_1359_; size_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_toApplicative_1350_ = lean_ctor_get(v_inst_1334_, 0);
v_vs_1351_ = lean_ctor_get(v_x_1336_, 0);
lean_inc_ref(v_vs_1351_);
lean_dec_ref_known(v_x_1336_, 1);
v_toBind_1352_ = lean_ctor_get(v_inst_1334_, 1);
lean_inc_n(v_toBind_1352_, 2);
v_toPure_1353_ = lean_ctor_get(v_toApplicative_1350_, 1);
v___x_1354_ = lean_box(0);
v___x_1355_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1353_, 2);
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1356_, 0, v_toPure_1353_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1357_, 0, v___x_1354_);
lean_closure_set(v___f_1357_, 1, v_toPure_1353_);
lean_closure_set(v___f_1357_, 2, v___x_1355_);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1358_, 0, v_f_1335_);
lean_closure_set(v___f_1358_, 1, v_toBind_1352_);
lean_closure_set(v___f_1358_, 2, v___f_1357_);
v_sz_1359_ = lean_array_size(v_vs_1351_);
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1334_, v_vs_1351_, v___f_1358_, v_sz_1359_, v___x_1360_, v___x_1355_);
v___x_1362_ = lean_apply_4(v_toBind_1352_, lean_box(0), lean_box(0), v___x_1361_, v___f_1356_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1363_, lean_object* v_f_1364_, lean_object* v_toBind_1365_, lean_object* v___f_1366_, lean_object* v_a_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1363_, v_f_1364_, v_a_1367_);
v___x_1371_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1370_, v___f_1366_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1372_, lean_object* v_m_1373_, lean_object* v_inst_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_f_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1374_, v_f_1376_, v_x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1379_, lean_object* v_____do__lift_1380_, lean_object* v_____s_1381_){
_start:
{
lean_object* v_fst_1382_; 
v_fst_1382_ = lean_ctor_get(v_____s_1381_, 0);
lean_inc(v_fst_1382_);
lean_dec_ref(v_____s_1381_);
if (lean_obj_tag(v_fst_1382_) == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_apply_2(v_toPure_1379_, lean_box(0), v_____do__lift_1380_);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1385_; 
lean_dec(v_____do__lift_1380_);
v_val_1384_ = lean_ctor_get(v_fst_1382_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v_fst_1382_, 1);
v___x_1385_ = lean_apply_2(v_toPure_1379_, lean_box(0), v_val_1384_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1386_, lean_object* v_toPure_1387_, lean_object* v___x_1388_, lean_object* v_____do__lift_1389_){
_start:
{
if (lean_obj_tag(v_____do__lift_1389_) == 1)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_____do__lift_1389_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1386_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
v___x_1393_ = lean_apply_2(v_toPure_1387_, lean_box(0), v___x_1392_);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec(v_____do__lift_1389_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1388_);
v___x_1395_ = lean_apply_2(v_toPure_1387_, lean_box(0), v___x_1394_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1396_, lean_object* v_toBind_1397_, lean_object* v___f_1398_, lean_object* v_a_1399_, lean_object* v_x_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_apply_1(v_f_1396_, v_a_1399_);
v___x_1403_ = lean_apply_4(v_toBind_1397_, lean_box(0), lean_box(0), v___x_1402_, v___f_1398_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1404_, lean_object* v_toBind_1405_, lean_object* v___f_1406_, lean_object* v_a_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1404_, v_toBind_1405_, v___f_1406_, v_a_1407_, v_x_1408_, v___y_1409_);
lean_dec_ref(v___y_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1411_, lean_object* v_f_1412_, lean_object* v_toBind_1413_, lean_object* v_tail_1414_, lean_object* v_inst_1415_, lean_object* v_____do__lift_1416_){
_start:
{
if (lean_obj_tag(v_____do__lift_1416_) == 0)
{
lean_object* v___f_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___f_1421_; size_t v_sz_1422_; size_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_inc(v_toPure_1411_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1417_, 0, v_toPure_1411_);
lean_closure_set(v___f_1417_, 1, v_____do__lift_1416_);
v___x_1418_ = lean_box(0);
v___x_1419_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1420_, 0, v___x_1418_);
lean_closure_set(v___f_1420_, 1, v_toPure_1411_);
lean_closure_set(v___f_1420_, 2, v___x_1419_);
lean_inc(v_toBind_1413_);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1421_, 0, v_f_1412_);
lean_closure_set(v___f_1421_, 1, v_toBind_1413_);
lean_closure_set(v___f_1421_, 2, v___f_1420_);
v_sz_1422_ = lean_array_size(v_tail_1414_);
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1415_, v_tail_1414_, v___f_1421_, v_sz_1422_, v___x_1423_, v___x_1419_);
v___x_1425_ = lean_apply_4(v_toBind_1413_, lean_box(0), lean_box(0), v___x_1424_, v___f_1417_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; 
lean_dec_ref(v_inst_1415_);
lean_dec_ref(v_tail_1414_);
lean_dec(v_toBind_1413_);
lean_dec(v_f_1412_);
v___x_1426_ = lean_apply_2(v_toPure_1411_, lean_box(0), v_____do__lift_1416_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1427_, lean_object* v_t_1428_, lean_object* v_f_1429_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toBind_1431_; lean_object* v_root_1432_; lean_object* v_tail_1433_; lean_object* v_toPure_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1427_, 0);
v_toBind_1431_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc_n(v_toBind_1431_, 2);
v_root_1432_ = lean_ctor_get(v_t_1428_, 0);
lean_inc_ref(v_root_1432_);
v_tail_1433_ = lean_ctor_get(v_t_1428_, 1);
lean_inc_ref(v_tail_1433_);
lean_dec_ref(v_t_1428_);
v_toPure_1434_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_inc(v_toPure_1434_);
lean_inc(v_f_1429_);
lean_inc_ref(v_inst_1427_);
v___x_1435_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1427_, v_f_1429_, v_root_1432_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1436_, 0, v_toPure_1434_);
lean_closure_set(v___f_1436_, 1, v_f_1429_);
lean_closure_set(v___f_1436_, 2, v_toBind_1431_);
lean_closure_set(v___f_1436_, 3, v_tail_1433_);
lean_closure_set(v___f_1436_, 4, v_inst_1427_);
v___x_1437_ = lean_apply_4(v_toBind_1431_, lean_box(0), lean_box(0), v___x_1435_, v___f_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1438_, lean_object* v_m_1439_, lean_object* v_inst_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_t_1442_, lean_object* v_f_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1440_, v_t_1442_, v_f_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1445_, lean_object* v_f_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v_cs_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_cs_1448_ = lean_ctor_get(v_x_1447_, 0);
lean_inc_ref(v_cs_1448_);
lean_dec_ref_known(v_x_1447_, 1);
lean_inc_ref(v_inst_1445_);
v___f_1449_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1449_, 0, v_inst_1445_);
lean_closure_set(v___f_1449_, 1, v_f_1446_);
v___x_1450_ = lean_array_get_size(v_cs_1448_);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1445_, v___f_1449_, v_cs_1448_, v___x_1450_, lean_box(0));
return v___x_1451_;
}
else
{
lean_object* v_vs_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_vs_1452_ = lean_ctor_get(v_x_1447_, 0);
lean_inc_ref(v_vs_1452_);
lean_dec_ref_known(v_x_1447_, 1);
v___x_1453_ = lean_array_get_size(v_vs_1452_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1445_, v_f_1446_, v_vs_1452_, v___x_1453_, lean_box(0));
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1455_, lean_object* v_f_1456_, lean_object* v_c_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1455_, v_f_1456_, v_c_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1459_, lean_object* v_m_1460_, lean_object* v_inst_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_f_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1461_, v_f_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1466_, lean_object* v_f_1467_, lean_object* v_root_1468_, lean_object* v_toPure_1469_, lean_object* v_____do__lift_1470_){
_start:
{
if (lean_obj_tag(v_____do__lift_1470_) == 0)
{
lean_object* v___x_1471_; 
lean_dec(v_toPure_1469_);
v___x_1471_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1466_, v_f_1467_, v_root_1468_);
return v___x_1471_;
}
else
{
lean_object* v___x_1472_; 
lean_dec_ref(v_root_1468_);
lean_dec(v_f_1467_);
lean_dec_ref(v_inst_1466_);
v___x_1472_ = lean_apply_2(v_toPure_1469_, lean_box(0), v_____do__lift_1470_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1473_, lean_object* v_t_1474_, lean_object* v_f_1475_){
_start:
{
lean_object* v_toApplicative_1476_; lean_object* v_toBind_1477_; lean_object* v_root_1478_; lean_object* v_tail_1479_; lean_object* v_toPure_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___f_1483_; lean_object* v___x_1484_; 
v_toApplicative_1476_ = lean_ctor_get(v_inst_1473_, 0);
v_toBind_1477_ = lean_ctor_get(v_inst_1473_, 1);
lean_inc(v_toBind_1477_);
v_root_1478_ = lean_ctor_get(v_t_1474_, 0);
lean_inc_ref(v_root_1478_);
v_tail_1479_ = lean_ctor_get(v_t_1474_, 1);
lean_inc_ref(v_tail_1479_);
lean_dec_ref(v_t_1474_);
v_toPure_1480_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_inc(v_toPure_1480_);
v___x_1481_ = lean_array_get_size(v_tail_1479_);
lean_inc(v_f_1475_);
lean_inc_ref(v_inst_1473_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1473_, v_f_1475_, v_tail_1479_, v___x_1481_, lean_box(0));
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1483_, 0, v_inst_1473_);
lean_closure_set(v___f_1483_, 1, v_f_1475_);
lean_closure_set(v___f_1483_, 2, v_root_1478_);
lean_closure_set(v___f_1483_, 3, v_toPure_1480_);
v___x_1484_ = lean_apply_4(v_toBind_1477_, lean_box(0), lean_box(0), v___x_1482_, v___f_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1485_, lean_object* v_m_1486_, lean_object* v_inst_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_t_1489_, lean_object* v_f_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1487_, v_t_1489_, v_f_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1492_, lean_object* v_x_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_apply_1(v_f_1492_, v___y_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1496_, lean_object* v_f_1497_, lean_object* v_x_1498_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_toApplicative_1499_; lean_object* v_cs_1500_; lean_object* v_toPure_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_toApplicative_1499_ = lean_ctor_get(v_inst_1496_, 0);
v_cs_1500_ = lean_ctor_get(v_x_1498_, 0);
lean_inc_ref(v_cs_1500_);
lean_dec_ref_known(v_x_1498_, 1);
v_toPure_1501_ = lean_ctor_get(v_toApplicative_1499_, 1);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_array_get_size(v_cs_1500_);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_nat_dec_lt(v___x_1502_, v___x_1503_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_inc(v_toPure_1501_);
lean_dec_ref(v_cs_1500_);
lean_dec(v_f_1497_);
lean_dec_ref(v_inst_1496_);
v___x_1506_ = lean_apply_2(v_toPure_1501_, lean_box(0), v___x_1504_);
return v___x_1506_;
}
else
{
lean_object* v___f_1507_; uint8_t v___x_1508_; 
lean_inc_ref(v_inst_1496_);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1507_, 0, v_inst_1496_);
lean_closure_set(v___f_1507_, 1, v_f_1497_);
v___x_1508_ = lean_nat_dec_le(v___x_1503_, v___x_1503_);
if (v___x_1508_ == 0)
{
if (v___x_1505_ == 0)
{
lean_object* v___x_1509_; 
lean_inc(v_toPure_1501_);
lean_dec_ref(v___f_1507_);
lean_dec_ref(v_cs_1500_);
lean_dec_ref(v_inst_1496_);
v___x_1509_ = lean_apply_2(v_toPure_1501_, lean_box(0), v___x_1504_);
return v___x_1509_;
}
else
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = lean_usize_of_nat(v___x_1503_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1496_, v___f_1507_, v_cs_1500_, v___x_1510_, v___x_1511_, v___x_1504_);
return v___x_1512_;
}
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1503_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1496_, v___f_1507_, v_cs_1500_, v___x_1513_, v___x_1514_, v___x_1504_);
return v___x_1515_;
}
}
}
else
{
lean_object* v_toApplicative_1516_; lean_object* v_vs_1517_; lean_object* v_toPure_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_toApplicative_1516_ = lean_ctor_get(v_inst_1496_, 0);
v_vs_1517_ = lean_ctor_get(v_x_1498_, 0);
lean_inc_ref(v_vs_1517_);
lean_dec_ref_known(v_x_1498_, 1);
v_toPure_1518_ = lean_ctor_get(v_toApplicative_1516_, 1);
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_array_get_size(v_vs_1517_);
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_nat_dec_lt(v___x_1519_, v___x_1520_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_inc(v_toPure_1518_);
lean_dec_ref(v_vs_1517_);
lean_dec(v_f_1497_);
lean_dec_ref(v_inst_1496_);
v___x_1523_ = lean_apply_2(v_toPure_1518_, lean_box(0), v___x_1521_);
return v___x_1523_;
}
else
{
lean_object* v___f_1524_; uint8_t v___x_1525_; 
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1524_, 0, v_f_1497_);
v___x_1525_ = lean_nat_dec_le(v___x_1520_, v___x_1520_);
if (v___x_1525_ == 0)
{
if (v___x_1522_ == 0)
{
lean_object* v___x_1526_; 
lean_inc(v_toPure_1518_);
lean_dec_ref(v___f_1524_);
lean_dec_ref(v_vs_1517_);
lean_dec_ref(v_inst_1496_);
v___x_1526_ = lean_apply_2(v_toPure_1518_, lean_box(0), v___x_1521_);
return v___x_1526_;
}
else
{
size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = lean_usize_of_nat(v___x_1520_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1496_, v___f_1524_, v_vs_1517_, v___x_1527_, v___x_1528_, v___x_1521_);
return v___x_1529_;
}
}
else
{
size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = ((size_t)0ULL);
v___x_1531_ = lean_usize_of_nat(v___x_1520_);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1496_, v___f_1524_, v_vs_1517_, v___x_1530_, v___x_1531_, v___x_1521_);
return v___x_1532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1533_, lean_object* v_f_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1533_, v_f_1534_, v___y_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1538_, lean_object* v_m_1539_, lean_object* v_inst_1540_, lean_object* v_f_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1540_, v_f_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_apply_1(v_f_1544_, v___y_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1548_, lean_object* v_toPure_1549_, lean_object* v_inst_1550_, lean_object* v___f_1551_, lean_object* v_x_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_get_size(v_tail_1548_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_dec(v___f_1551_);
lean_dec_ref(v_inst_1550_);
lean_dec_ref(v_tail_1548_);
v___x_1557_ = lean_apply_2(v_toPure_1549_, lean_box(0), v___x_1555_);
return v___x_1557_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_nat_dec_le(v___x_1554_, v___x_1554_);
if (v___x_1558_ == 0)
{
if (v___x_1556_ == 0)
{
lean_object* v___x_1559_; 
lean_dec(v___f_1551_);
lean_dec_ref(v_inst_1550_);
lean_dec_ref(v_tail_1548_);
v___x_1559_ = lean_apply_2(v_toPure_1549_, lean_box(0), v___x_1555_);
return v___x_1559_;
}
else
{
size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v_toPure_1549_);
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = lean_usize_of_nat(v___x_1554_);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1550_, v___f_1551_, v_tail_1548_, v___x_1560_, v___x_1561_, v___x_1555_);
return v___x_1562_;
}
}
else
{
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v_toPure_1549_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = lean_usize_of_nat(v___x_1554_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1550_, v___f_1551_, v_tail_1548_, v___x_1563_, v___x_1564_, v___x_1555_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1566_, lean_object* v_t_1567_, lean_object* v_f_1568_){
_start:
{
lean_object* v_toApplicative_1569_; lean_object* v_toPure_1570_; lean_object* v_toSeqRight_1571_; lean_object* v_root_1572_; lean_object* v_tail_1573_; lean_object* v___f_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_toApplicative_1569_ = lean_ctor_get(v_inst_1566_, 0);
v_toPure_1570_ = lean_ctor_get(v_toApplicative_1569_, 1);
v_toSeqRight_1571_ = lean_ctor_get(v_toApplicative_1569_, 4);
lean_inc(v_toSeqRight_1571_);
v_root_1572_ = lean_ctor_get(v_t_1567_, 0);
lean_inc_ref(v_root_1572_);
v_tail_1573_ = lean_ctor_get(v_t_1567_, 1);
lean_inc_ref(v_tail_1573_);
lean_dec_ref(v_t_1567_);
lean_inc(v_f_1568_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1574_, 0, v_f_1568_);
lean_inc_ref(v_inst_1566_);
lean_inc(v_toPure_1570_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1575_, 0, v_tail_1573_);
lean_closure_set(v___f_1575_, 1, v_toPure_1570_);
lean_closure_set(v___f_1575_, 2, v_inst_1566_);
lean_closure_set(v___f_1575_, 3, v___f_1574_);
v___x_1576_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1566_, v_f_1568_, v_root_1572_);
v___x_1577_ = lean_apply_4(v_toSeqRight_1571_, lean_box(0), lean_box(0), v___x_1576_, v___f_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1578_, lean_object* v_m_1579_, lean_object* v_inst_1580_, lean_object* v_t_1581_, lean_object* v_f_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1580_, v_t_1581_, v_f_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_toApplicative_1584_, lean_object* v_j_1585_, lean_object* v_cs_1586_, lean_object* v_inst_1587_, lean_object* v___f_1588_, lean_object* v_____r_1589_){
_start:
{
lean_object* v_toPure_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_toPure_1590_ = lean_ctor_get(v_toApplicative_1584_, 1);
lean_inc(v_toPure_1590_);
lean_dec_ref(v_toApplicative_1584_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_add(v_j_1585_, v___x_1591_);
v___x_1593_ = lean_array_get_size(v_cs_1586_);
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_nat_dec_lt(v___x_1592_, v___x_1593_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v___x_1592_);
lean_dec(v___f_1588_);
lean_dec_ref(v_inst_1587_);
lean_dec_ref(v_cs_1586_);
v___x_1596_ = lean_apply_2(v_toPure_1590_, lean_box(0), v___x_1594_);
return v___x_1596_;
}
else
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_nat_dec_le(v___x_1593_, v___x_1593_);
if (v___x_1597_ == 0)
{
if (v___x_1595_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v___x_1592_);
lean_dec(v___f_1588_);
lean_dec_ref(v_inst_1587_);
lean_dec_ref(v_cs_1586_);
v___x_1598_ = lean_apply_2(v_toPure_1590_, lean_box(0), v___x_1594_);
return v___x_1598_;
}
else
{
size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_toPure_1590_);
v___x_1599_ = lean_usize_of_nat(v___x_1592_);
lean_dec(v___x_1592_);
v___x_1600_ = lean_usize_of_nat(v___x_1593_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1587_, v___f_1588_, v_cs_1586_, v___x_1599_, v___x_1600_, v___x_1594_);
return v___x_1601_;
}
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_toPure_1590_);
v___x_1602_ = lean_usize_of_nat(v___x_1592_);
lean_dec(v___x_1592_);
v___x_1603_ = lean_usize_of_nat(v___x_1593_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1587_, v___f_1588_, v_cs_1586_, v___x_1602_, v___x_1603_, v___x_1594_);
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_1605_, lean_object* v_j_1606_, lean_object* v_cs_1607_, lean_object* v_inst_1608_, lean_object* v___f_1609_, lean_object* v_____r_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_toApplicative_1605_, v_j_1606_, v_cs_1607_, v_inst_1608_, v___f_1609_, v_____r_1610_);
lean_dec(v_j_1606_);
return v_res_1611_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1612_, lean_object* v_f_1613_, lean_object* v_x_1614_, size_t v_x_1615_, size_t v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1614_) == 0)
{
lean_object* v_toApplicative_1617_; lean_object* v_toBind_1618_; lean_object* v_cs_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; size_t v___x_1622_; lean_object* v_j_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_toApplicative_1617_ = lean_ctor_get(v_inst_1612_, 0);
v_toBind_1618_ = lean_ctor_get(v_inst_1612_, 1);
lean_inc(v_toBind_1618_);
v_cs_1619_ = lean_ctor_get(v_x_1614_, 0);
lean_inc_ref_n(v_cs_1619_, 2);
lean_dec_ref_known(v_x_1614_, 1);
lean_inc(v_f_1613_);
lean_inc_ref_n(v_inst_1612_, 2);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1620_, 0, v_inst_1612_);
lean_closure_set(v___f_1620_, 1, v_f_1613_);
v___x_1621_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1622_ = lean_usize_shift_right(v_x_1615_, v_x_1616_);
v_j_1623_ = lean_usize_to_nat(v___x_1622_);
lean_inc(v_j_1623_);
lean_inc_ref(v_toApplicative_1617_);
v___f_1624_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1624_, 0, v_toApplicative_1617_);
lean_closure_set(v___f_1624_, 1, v_j_1623_);
lean_closure_set(v___f_1624_, 2, v_cs_1619_);
lean_closure_set(v___f_1624_, 3, v_inst_1612_);
lean_closure_set(v___f_1624_, 4, v___f_1620_);
v___x_1625_ = lean_array_get(v___x_1621_, v_cs_1619_, v_j_1623_);
lean_dec(v_j_1623_);
lean_dec_ref(v_cs_1619_);
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_shift_left(v___x_1626_, v_x_1616_);
v___x_1628_ = lean_usize_sub(v___x_1627_, v___x_1626_);
v___x_1629_ = lean_usize_land(v_x_1615_, v___x_1628_);
v___x_1630_ = ((size_t)5ULL);
v___x_1631_ = lean_usize_sub(v_x_1616_, v___x_1630_);
v___x_1632_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1612_, v_f_1613_, v___x_1625_, v___x_1629_, v___x_1631_);
v___x_1633_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1632_, v___f_1624_);
return v___x_1633_;
}
else
{
lean_object* v_toApplicative_1634_; lean_object* v_vs_1635_; lean_object* v_toPure_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_toApplicative_1634_ = lean_ctor_get(v_inst_1612_, 0);
v_vs_1635_ = lean_ctor_get(v_x_1614_, 0);
lean_inc_ref(v_vs_1635_);
lean_dec_ref_known(v_x_1614_, 1);
v_toPure_1636_ = lean_ctor_get(v_toApplicative_1634_, 1);
v___x_1637_ = lean_usize_to_nat(v_x_1615_);
v___x_1638_ = lean_array_get_size(v_vs_1635_);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_nat_dec_lt(v___x_1637_, v___x_1638_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_inc(v_toPure_1636_);
lean_dec(v___x_1637_);
lean_dec_ref(v_vs_1635_);
lean_dec(v_f_1613_);
lean_dec_ref(v_inst_1612_);
v___x_1641_ = lean_apply_2(v_toPure_1636_, lean_box(0), v___x_1639_);
return v___x_1641_;
}
else
{
lean_object* v___f_1642_; uint8_t v___x_1643_; 
v___f_1642_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1642_, 0, v_f_1613_);
v___x_1643_ = lean_nat_dec_le(v___x_1638_, v___x_1638_);
if (v___x_1643_ == 0)
{
if (v___x_1640_ == 0)
{
lean_object* v___x_1644_; 
lean_inc(v_toPure_1636_);
lean_dec_ref(v___f_1642_);
lean_dec(v___x_1637_);
lean_dec_ref(v_vs_1635_);
lean_dec_ref(v_inst_1612_);
v___x_1644_ = lean_apply_2(v_toPure_1636_, lean_box(0), v___x_1639_);
return v___x_1644_;
}
else
{
size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_usize_of_nat(v___x_1637_);
lean_dec(v___x_1637_);
v___x_1646_ = lean_usize_of_nat(v___x_1638_);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1612_, v___f_1642_, v_vs_1635_, v___x_1645_, v___x_1646_, v___x_1639_);
return v___x_1647_;
}
}
else
{
size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_usize_of_nat(v___x_1637_);
lean_dec(v___x_1637_);
v___x_1649_ = lean_usize_of_nat(v___x_1638_);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1612_, v___f_1642_, v_vs_1635_, v___x_1648_, v___x_1649_, v___x_1639_);
return v___x_1650_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1612_ = stack[0].m_obj;
lean_object* v_f_1613_ = stack[1].m_obj;
lean_object* v_x_1614_ = stack[2].m_obj;
size_t v_x_1615_ = stack[3].m_num;
size_t v_x_1616_ = stack[4].m_num;
lean_object* v_res_1651_;
v_res_1651_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1612_, v_f_1613_, v_x_1614_, v_x_1615_, v_x_1616_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1652_, lean_object* v_f_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
size_t v_x_294__boxed_1657_; size_t v_x_295__boxed_1658_; lean_object* v_res_1659_; 
v_x_294__boxed_1657_ = lean_unbox_usize(v_x_1655_);
lean_dec(v_x_1655_);
v_x_295__boxed_1658_ = lean_unbox_usize(v_x_1656_);
lean_dec(v_x_1656_);
v_res_1659_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1652_, v_f_1653_, v_x_1654_, v_x_294__boxed_1657_, v_x_295__boxed_1658_);
return v_res_1659_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1660_, lean_object* v_m_1661_, lean_object* v_inst_1662_, lean_object* v_f_1663_, lean_object* v_x_1664_, size_t v_x_1665_, size_t v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1662_, v_f_1663_, v_x_1664_, v_x_1665_, v_x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1662_ = stack[2].m_obj;
lean_object* v_f_1663_ = stack[3].m_obj;
lean_object* v_x_1664_ = stack[4].m_obj;
size_t v_x_1665_ = stack[5].m_num;
size_t v_x_1666_ = stack[6].m_num;
lean_object* v_res_1668_;
v_res_1668_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_box(0), lean_box(0), v_inst_1662_, v_f_1663_, v_x_1664_, v_x_1665_, v_x_1666_);
stack->m_obj
 = v_res_1668_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_m_1670_, lean_object* v_inst_1671_, lean_object* v_f_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
size_t v_x_401__boxed_1676_; size_t v_x_402__boxed_1677_; lean_object* v_res_1678_; 
v_x_401__boxed_1676_ = lean_unbox_usize(v_x_1674_);
lean_dec(v_x_1674_);
v_x_402__boxed_1677_ = lean_unbox_usize(v_x_1675_);
lean_dec(v_x_1675_);
v_res_1678_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1669_, v_m_1670_, v_inst_1671_, v_f_1672_, v_x_1673_, v_x_401__boxed_1676_, v_x_402__boxed_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_toApplicative_1679_, lean_object* v_tail_1680_, lean_object* v___x_1681_, lean_object* v_inst_1682_, lean_object* v___f_1683_, lean_object* v_____r_1684_){
_start:
{
lean_object* v_toPure_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_toPure_1685_ = lean_ctor_get(v_toApplicative_1679_, 1);
lean_inc(v_toPure_1685_);
lean_dec_ref(v_toApplicative_1679_);
v___x_1686_ = lean_array_get_size(v_tail_1680_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_nat_dec_lt(v___x_1681_, v___x_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_dec(v___f_1683_);
lean_dec_ref(v_inst_1682_);
lean_dec_ref(v_tail_1680_);
v___x_1689_ = lean_apply_2(v_toPure_1685_, lean_box(0), v___x_1687_);
return v___x_1689_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_le(v___x_1686_, v___x_1686_);
if (v___x_1690_ == 0)
{
if (v___x_1688_ == 0)
{
lean_object* v___x_1691_; 
lean_dec(v___f_1683_);
lean_dec_ref(v_inst_1682_);
lean_dec_ref(v_tail_1680_);
v___x_1691_ = lean_apply_2(v_toPure_1685_, lean_box(0), v___x_1687_);
return v___x_1691_;
}
else
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v_toPure_1685_);
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1686_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1682_, v___f_1683_, v_tail_1680_, v___x_1692_, v___x_1693_, v___x_1687_);
return v___x_1694_;
}
}
else
{
size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_toPure_1685_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = lean_usize_of_nat(v___x_1686_);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1682_, v___f_1683_, v_tail_1680_, v___x_1695_, v___x_1696_, v___x_1687_);
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_toApplicative_1698_, lean_object* v_tail_1699_, lean_object* v___x_1700_, lean_object* v_inst_1701_, lean_object* v___f_1702_, lean_object* v_____r_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_toApplicative_1698_, v_tail_1699_, v___x_1700_, v_inst_1701_, v___f_1702_, v_____r_1703_);
lean_dec(v___x_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1705_, lean_object* v_t_1706_, lean_object* v_f_1707_, lean_object* v_start_1708_){
_start:
{
lean_object* v_toApplicative_1709_; lean_object* v_toBind_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_toApplicative_1709_ = lean_ctor_get(v_inst_1705_, 0);
v_toBind_1710_ = lean_ctor_get(v_inst_1705_, 1);
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_nat_dec_eq(v_start_1708_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v_root_1713_; lean_object* v_tail_1714_; size_t v_shift_1715_; lean_object* v_tailOff_1716_; uint8_t v___x_1717_; 
v_root_1713_ = lean_ctor_get(v_t_1706_, 0);
lean_inc_ref(v_root_1713_);
v_tail_1714_ = lean_ctor_get(v_t_1706_, 1);
lean_inc_ref(v_tail_1714_);
v_shift_1715_ = lean_ctor_get_usize(v_t_1706_, 4);
v_tailOff_1716_ = lean_ctor_get(v_t_1706_, 3);
lean_inc(v_tailOff_1716_);
lean_dec_ref(v_t_1706_);
v___x_1717_ = lean_nat_dec_le(v_tailOff_1716_, v_start_1708_);
if (v___x_1717_ == 0)
{
lean_object* v___f_1718_; lean_object* v___f_1719_; size_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_inc(v_toBind_1710_);
lean_dec(v_tailOff_1716_);
lean_inc(v_f_1707_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1718_, 0, v_f_1707_);
lean_inc_ref(v_inst_1705_);
lean_inc_ref(v_toApplicative_1709_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1719_, 0, v_toApplicative_1709_);
lean_closure_set(v___f_1719_, 1, v_tail_1714_);
lean_closure_set(v___f_1719_, 2, v___x_1711_);
lean_closure_set(v___f_1719_, 3, v_inst_1705_);
lean_closure_set(v___f_1719_, 4, v___f_1718_);
v___x_1720_ = lean_usize_of_nat(v_start_1708_);
v___x_1721_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1705_, v_f_1707_, v_root_1713_, v___x_1720_, v_shift_1715_);
v___x_1722_ = lean_apply_4(v_toBind_1710_, lean_box(0), lean_box(0), v___x_1721_, v___f_1719_);
return v___x_1722_;
}
else
{
lean_object* v_toPure_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
lean_dec_ref(v_root_1713_);
v_toPure_1723_ = lean_ctor_get(v_toApplicative_1709_, 1);
v___x_1724_ = lean_nat_sub(v_start_1708_, v_tailOff_1716_);
lean_dec(v_tailOff_1716_);
v___x_1725_ = lean_array_get_size(v_tail_1714_);
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_nat_dec_lt(v___x_1724_, v___x_1725_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
lean_inc(v_toPure_1723_);
lean_dec(v___x_1724_);
lean_dec_ref(v_tail_1714_);
lean_dec(v_f_1707_);
lean_dec_ref(v_inst_1705_);
v___x_1728_ = lean_apply_2(v_toPure_1723_, lean_box(0), v___x_1726_);
return v___x_1728_;
}
else
{
lean_object* v___f_1729_; uint8_t v___x_1730_; 
v___f_1729_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1729_, 0, v_f_1707_);
v___x_1730_ = lean_nat_dec_le(v___x_1725_, v___x_1725_);
if (v___x_1730_ == 0)
{
if (v___x_1727_ == 0)
{
lean_object* v___x_1731_; 
lean_inc(v_toPure_1723_);
lean_dec_ref(v___f_1729_);
lean_dec(v___x_1724_);
lean_dec_ref(v_tail_1714_);
lean_dec_ref(v_inst_1705_);
v___x_1731_ = lean_apply_2(v_toPure_1723_, lean_box(0), v___x_1726_);
return v___x_1731_;
}
else
{
size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_usize_of_nat(v___x_1724_);
lean_dec(v___x_1724_);
v___x_1733_ = lean_usize_of_nat(v___x_1725_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1705_, v___f_1729_, v_tail_1714_, v___x_1732_, v___x_1733_, v___x_1726_);
return v___x_1734_;
}
}
else
{
size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_usize_of_nat(v___x_1724_);
lean_dec(v___x_1724_);
v___x_1736_ = lean_usize_of_nat(v___x_1725_);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1705_, v___f_1729_, v_tail_1714_, v___x_1735_, v___x_1736_, v___x_1726_);
return v___x_1737_;
}
}
}
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1705_, v_t_1706_, v_f_1707_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1739_, lean_object* v_t_1740_, lean_object* v_f_1741_, lean_object* v_start_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_PersistentArray_forM___redArg(v_inst_1739_, v_t_1740_, v_f_1741_, v_start_1742_);
lean_dec(v_start_1742_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1744_, lean_object* v_m_1745_, lean_object* v_inst_1746_, lean_object* v_t_1747_, lean_object* v_f_1748_, lean_object* v_start_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_PersistentArray_forM___redArg(v_inst_1746_, v_t_1747_, v_f_1748_, v_start_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_m_1752_, lean_object* v_inst_1753_, lean_object* v_t_1754_, lean_object* v_f_1755_, lean_object* v_start_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_PersistentArray_forM(v_00_u03b1_1751_, v_m_1752_, v_inst_1753_, v_t_1754_, v_f_1755_, v_start_1756_);
lean_dec(v_start_1756_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1758_, lean_object* v_x1_1759_, lean_object* v_x2_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_apply_2(v_f_1758_, v_x1_1759_, v_x2_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1781_, lean_object* v_f_1782_, lean_object* v_init_1783_, lean_object* v_start_1784_){
_start:
{
lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1785_, 0, v_f_1782_);
v___x_1786_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1787_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1786_, v_t_1781_, v___f_1785_, v_init_1783_, v_start_1784_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1788_, lean_object* v_f_1789_, lean_object* v_init_1790_, lean_object* v_start_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_PersistentArray_foldl___redArg(v_t_1788_, v_f_1789_, v_init_1790_, v_start_1791_);
lean_dec(v_start_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_t_1795_, lean_object* v_f_1796_, lean_object* v_init_1797_, lean_object* v_start_1798_){
_start:
{
lean_object* v___f_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___f_1799_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1799_, 0, v_f_1796_);
v___x_1800_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1801_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1800_, v_t_1795_, v___f_1799_, v_init_1797_, v_start_1798_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_t_1804_, lean_object* v_f_1805_, lean_object* v_init_1806_, lean_object* v_start_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1802_, v_00_u03b2_1803_, v_t_1804_, v_f_1805_, v_init_1806_, v_start_1807_);
lean_dec(v_start_1807_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1809_, lean_object* v_f_1810_, lean_object* v_init_1811_){
_start:
{
lean_object* v___f_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1812_, 0, v_f_1810_);
v___x_1813_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1814_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1813_, v_t_1809_, v___f_1812_, v_init_1811_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1815_, lean_object* v_00_u03b2_1816_, lean_object* v_t_1817_, lean_object* v_f_1818_, lean_object* v_init_1819_){
_start:
{
lean_object* v___f_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___f_1820_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1820_, 0, v_f_1818_);
v___x_1821_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1822_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1821_, v_t_1817_, v___f_1820_, v_init_1819_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1823_, lean_object* v_x1_1824_, lean_object* v_x2_1825_){
_start:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
lean_inc(v_x2_1825_);
v___x_1826_ = lean_apply_1(v_p_1823_, v_x2_1825_);
v___x_1827_ = lean_unbox(v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec(v_x2_1825_);
return v_x1_1824_;
}
else
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_PersistentArray_push___redArg(v_x1_1824_, v_x2_1825_);
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1829_, lean_object* v_p_1830_){
_start:
{
lean_object* v___f_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1831_, 0, v_p_1830_);
v___x_1832_ = lean_unsigned_to_nat(32u);
v___x_1833_ = lean_mk_empty_array_with_capacity(v___x_1832_);
lean_dec_ref(v___x_1833_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1836_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1837_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1836_, v_as_1829_, v___f_1831_, v___x_1835_, v___x_1834_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1838_, lean_object* v_as_1839_, lean_object* v_p_1840_){
_start:
{
lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1841_, 0, v_p_1840_);
v___x_1842_ = lean_unsigned_to_nat(32u);
v___x_1843_ = lean_mk_empty_array_with_capacity(v___x_1842_);
lean_dec_ref(v___x_1843_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1846_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1847_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1846_, v_as_1839_, v___f_1841_, v___x_1845_, v___x_1844_);
return v___x_1847_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1848_, size_t v_i_1849_, size_t v_stop_1850_, lean_object* v_b_1851_){
_start:
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_usize_dec_eq(v_i_1849_, v_stop_1850_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; size_t v___x_1855_; size_t v___x_1856_; 
v___x_1853_ = lean_array_uget_borrowed(v_as_1848_, v_i_1849_);
lean_inc(v___x_1853_);
v___x_1854_ = lean_array_push(v_b_1851_, v___x_1853_);
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1849_, v___x_1855_);
v_i_1849_ = v___x_1856_;
v_b_1851_ = v___x_1854_;
goto _start;
}
else
{
return v_b_1851_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1848_ = stack[0].m_obj;
size_t v_i_1849_ = stack[1].m_num;
size_t v_stop_1850_ = stack[2].m_num;
lean_object* v_b_1851_ = stack[3].m_obj;
lean_object* v_res_1858_;
v_res_1858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1848_, v_i_1849_, v_stop_1850_, v_b_1851_);
stack->m_obj
 = v_res_1858_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1859_, lean_object* v_i_1860_, lean_object* v_stop_1861_, lean_object* v_b_1862_){
_start:
{
size_t v_i_boxed_1863_; size_t v_stop_boxed_1864_; lean_object* v_res_1865_; 
v_i_boxed_1863_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_stop_boxed_1864_ = lean_unbox_usize(v_stop_1861_);
lean_dec(v_stop_1861_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1859_, v_i_boxed_1863_, v_stop_boxed_1864_, v_b_1862_);
lean_dec_ref(v_as_1859_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
lean_object* v_cs_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_cs_1868_ = lean_ctor_get(v_x_1866_, 0);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_array_get_size(v_cs_1868_);
v___x_1871_ = lean_nat_dec_lt(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
return v_x_1867_;
}
else
{
size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((size_t)0ULL);
v___x_1873_ = lean_usize_of_nat(v___x_1870_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1868_, v___x_1872_, v___x_1873_, v_x_1867_);
return v___x_1874_;
}
}
else
{
lean_object* v_vs_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_vs_1875_ = lean_ctor_get(v_x_1866_, 0);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_array_get_size(v_vs_1875_);
v___x_1878_ = lean_nat_dec_lt(v___x_1876_, v___x_1877_);
if (v___x_1878_ == 0)
{
return v_x_1867_;
}
else
{
size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = lean_usize_of_nat(v___x_1877_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1875_, v___x_1879_, v___x_1880_, v_x_1867_);
return v___x_1881_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1882_, size_t v_i_1883_, size_t v_stop_1884_, lean_object* v_b_1885_){
_start:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_eq(v_i_1883_, v_stop_1884_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; 
v___x_1887_ = lean_array_uget_borrowed(v_as_1882_, v_i_1883_);
v___x_1888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1887_, v_b_1885_);
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1883_, v___x_1889_);
v_i_1883_ = v___x_1890_;
v_b_1885_ = v___x_1888_;
goto _start;
}
else
{
return v_b_1885_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1882_ = stack[0].m_obj;
size_t v_i_1883_ = stack[1].m_num;
size_t v_stop_1884_ = stack[2].m_num;
lean_object* v_b_1885_ = stack[3].m_obj;
lean_object* v_res_1892_;
v_res_1892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1882_, v_i_1883_, v_stop_1884_, v_b_1885_);
stack->m_obj
 = v_res_1892_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1893_, lean_object* v_i_1894_, lean_object* v_stop_1895_, lean_object* v_b_1896_){
_start:
{
size_t v_i_boxed_1897_; size_t v_stop_boxed_1898_; lean_object* v_res_1899_; 
v_i_boxed_1897_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_stop_boxed_1898_ = lean_unbox_usize(v_stop_1895_);
lean_dec(v_stop_1895_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1893_, v_i_boxed_1897_, v_stop_boxed_1898_, v_b_1896_);
lean_dec_ref(v_as_1893_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1900_, v_x_1901_);
lean_dec_ref(v_x_1900_);
return v_res_1902_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1903_, size_t v_x_1904_, size_t v_x_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1903_) == 0)
{
lean_object* v_cs_1907_; lean_object* v___x_1908_; size_t v___x_1909_; lean_object* v_j_1910_; lean_object* v___x_1911_; size_t v___x_1912_; size_t v___x_1913_; size_t v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_cs_1907_ = lean_ctor_get(v_x_1903_, 0);
v___x_1908_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1909_ = lean_usize_shift_right(v_x_1904_, v_x_1905_);
v_j_1910_ = lean_usize_to_nat(v___x_1909_);
v___x_1911_ = lean_array_get_borrowed(v___x_1908_, v_cs_1907_, v_j_1910_);
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_shift_left(v___x_1912_, v_x_1905_);
v___x_1914_ = lean_usize_sub(v___x_1913_, v___x_1912_);
v___x_1915_ = lean_usize_land(v_x_1904_, v___x_1914_);
v___x_1916_ = ((size_t)5ULL);
v___x_1917_ = lean_usize_sub(v_x_1905_, v___x_1916_);
v___x_1918_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1911_, v___x_1915_, v___x_1917_, v_x_1906_);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_nat_add(v_j_1910_, v___x_1919_);
lean_dec(v_j_1910_);
v___x_1921_ = lean_array_get_size(v_cs_1907_);
v___x_1922_ = lean_nat_dec_lt(v___x_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec(v___x_1920_);
return v___x_1918_;
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_usize_of_nat(v___x_1920_);
lean_dec(v___x_1920_);
v___x_1924_ = lean_usize_of_nat(v___x_1921_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1907_, v___x_1923_, v___x_1924_, v___x_1918_);
return v___x_1925_;
}
}
else
{
lean_object* v_vs_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_vs_1926_ = lean_ctor_get(v_x_1903_, 0);
v___x_1927_ = lean_usize_to_nat(v_x_1904_);
v___x_1928_ = lean_array_get_size(v_vs_1926_);
v___x_1929_ = lean_nat_dec_lt(v___x_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec(v___x_1927_);
return v_x_1906_;
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_usize_of_nat(v___x_1927_);
lean_dec(v___x_1927_);
v___x_1931_ = lean_usize_of_nat(v___x_1928_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1926_, v___x_1930_, v___x_1931_, v_x_1906_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1903_ = stack[0].m_obj;
size_t v_x_1904_ = stack[1].m_num;
size_t v_x_1905_ = stack[2].m_num;
lean_object* v_x_1906_ = stack[3].m_obj;
lean_object* v_res_1933_;
v_res_1933_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1903_, v_x_1904_, v_x_1905_, v_x_1906_);
stack->m_obj
 = v_res_1933_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1934_, lean_object* v_x_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
size_t v_x_1148__boxed_1938_; size_t v_x_1149__boxed_1939_; lean_object* v_res_1940_; 
v_x_1148__boxed_1938_ = lean_unbox_usize(v_x_1935_);
lean_dec(v_x_1935_);
v_x_1149__boxed_1939_ = lean_unbox_usize(v_x_1936_);
lean_dec(v_x_1936_);
v_res_1940_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1934_, v_x_1148__boxed_1938_, v_x_1149__boxed_1939_, v_x_1937_);
lean_dec_ref(v_x_1934_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1941_, lean_object* v_init_1942_, lean_object* v_start_1943_){
_start:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_nat_dec_eq(v_start_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v_root_1946_; lean_object* v_tail_1947_; size_t v_shift_1948_; lean_object* v_tailOff_1949_; uint8_t v___x_1950_; 
v_root_1946_ = lean_ctor_get(v_t_1941_, 0);
v_tail_1947_ = lean_ctor_get(v_t_1941_, 1);
v_shift_1948_ = lean_ctor_get_usize(v_t_1941_, 4);
v_tailOff_1949_ = lean_ctor_get(v_t_1941_, 3);
v___x_1950_ = lean_nat_dec_le(v_tailOff_1949_, v_start_1943_);
if (v___x_1950_ == 0)
{
size_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1951_ = lean_usize_of_nat(v_start_1943_);
v___x_1952_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1946_, v___x_1951_, v_shift_1948_, v_init_1942_);
v___x_1953_ = lean_array_get_size(v_tail_1947_);
v___x_1954_ = lean_nat_dec_lt(v___x_1944_, v___x_1953_);
if (v___x_1954_ == 0)
{
return v___x_1952_;
}
else
{
size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = lean_usize_of_nat(v___x_1953_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1947_, v___x_1955_, v___x_1956_, v___x_1952_);
return v___x_1957_;
}
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_nat_sub(v_start_1943_, v_tailOff_1949_);
v___x_1959_ = lean_array_get_size(v_tail_1947_);
v___x_1960_ = lean_nat_dec_lt(v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_dec(v___x_1958_);
return v_init_1942_;
}
else
{
size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_usize_of_nat(v___x_1958_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_usize_of_nat(v___x_1959_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1947_, v___x_1961_, v___x_1962_, v_init_1942_);
return v___x_1963_;
}
}
}
else
{
lean_object* v_root_1964_; lean_object* v_tail_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_root_1964_ = lean_ctor_get(v_t_1941_, 0);
v_tail_1965_ = lean_ctor_get(v_t_1941_, 1);
v___x_1966_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1964_, v_init_1942_);
v___x_1967_ = lean_array_get_size(v_tail_1965_);
v___x_1968_ = lean_nat_dec_lt(v___x_1944_, v___x_1967_);
if (v___x_1968_ == 0)
{
return v___x_1966_;
}
else
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1967_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1965_, v___x_1969_, v___x_1970_, v___x_1966_);
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1972_, lean_object* v_init_1973_, lean_object* v_start_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1972_, v_init_1973_, v_start_1974_);
lean_dec(v_start_1974_);
lean_dec_ref(v_t_1972_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1979_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1976_, v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_PersistentArray_toArray___redArg(v_t_1980_);
lean_dec_ref(v_t_1980_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1982_, lean_object* v_t_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_PersistentArray_toArray___redArg(v_t_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1985_, lean_object* v_t_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1985_, v_t_1986_);
lean_dec_ref(v_t_1986_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1988_, lean_object* v_t_1989_, lean_object* v_init_1990_, lean_object* v_start_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1989_, v_init_1990_, v_start_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1993_, lean_object* v_t_1994_, lean_object* v_init_1995_, lean_object* v_start_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1993_, v_t_1994_, v_init_1995_, v_start_1996_);
lean_dec(v_start_1996_);
lean_dec_ref(v_t_1994_);
return v_res_1997_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1998_, lean_object* v_x_1999_, size_t v_x_2000_, size_t v_x_2001_, lean_object* v_x_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1999_, v_x_2000_, v_x_2001_, v_x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1999_ = stack[1].m_obj;
size_t v_x_2000_ = stack[2].m_num;
size_t v_x_2001_ = stack[3].m_num;
lean_object* v_x_2002_ = stack[4].m_obj;
lean_object* v_res_2004_;
v_res_2004_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_box(0), v_x_1999_, v_x_2000_, v_x_2001_, v_x_2002_);
stack->m_obj
 = v_res_2004_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_){
_start:
{
size_t v_x_1326__boxed_2010_; size_t v_x_1327__boxed_2011_; lean_object* v_res_2012_; 
v_x_1326__boxed_2010_ = lean_unbox_usize(v_x_2007_);
lean_dec(v_x_2007_);
v_x_1327__boxed_2011_ = lean_unbox_usize(v_x_2008_);
lean_dec(v_x_2008_);
v_res_2012_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_2005_, v_x_2006_, v_x_1326__boxed_2010_, v_x_1327__boxed_2011_, v_x_2009_);
lean_dec_ref(v_x_2006_);
return v_res_2012_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_2013_, lean_object* v_as_2014_, size_t v_i_2015_, size_t v_stop_2016_, lean_object* v_b_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_2014_, v_i_2015_, v_stop_2016_, v_b_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2014_ = stack[1].m_obj;
size_t v_i_2015_ = stack[2].m_num;
size_t v_stop_2016_ = stack[3].m_num;
lean_object* v_b_2017_ = stack[4].m_obj;
lean_object* v_res_2019_;
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_box(0), v_as_2014_, v_i_2015_, v_stop_2016_, v_b_2017_);
stack->m_obj
 = v_res_2019_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_as_2021_, lean_object* v_i_2022_, lean_object* v_stop_2023_, lean_object* v_b_2024_){
_start:
{
size_t v_i_boxed_2025_; size_t v_stop_boxed_2026_; lean_object* v_res_2027_; 
v_i_boxed_2025_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_stop_boxed_2026_ = lean_unbox_usize(v_stop_2023_);
lean_dec(v_stop_2023_);
v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_2020_, v_as_2021_, v_i_boxed_2025_, v_stop_boxed_2026_, v_b_2024_);
lean_dec_ref(v_as_2021_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_2029_, v_x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_2032_, v_x_2033_, v_x_2034_);
lean_dec_ref(v_x_2033_);
return v_res_2035_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2036_, lean_object* v_as_2037_, size_t v_i_2038_, size_t v_stop_2039_, lean_object* v_b_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_2037_, v_i_2038_, v_stop_2039_, v_b_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2037_ = stack[1].m_obj;
size_t v_i_2038_ = stack[2].m_num;
size_t v_stop_2039_ = stack[3].m_num;
lean_object* v_b_2040_ = stack[4].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_box(0), v_as_2037_, v_i_2038_, v_stop_2039_, v_b_2040_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2043_, lean_object* v_as_2044_, lean_object* v_i_2045_, lean_object* v_stop_2046_, lean_object* v_b_2047_){
_start:
{
size_t v_i_boxed_2048_; size_t v_stop_boxed_2049_; lean_object* v_res_2050_; 
v_i_boxed_2048_ = lean_unbox_usize(v_i_2045_);
lean_dec(v_i_2045_);
v_stop_boxed_2049_ = lean_unbox_usize(v_stop_2046_);
lean_dec(v_stop_2046_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_2043_, v_as_2044_, v_i_boxed_2048_, v_stop_boxed_2049_, v_b_2047_);
lean_dec_ref(v_as_2044_);
return v_res_2050_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_2051_, size_t v_i_2052_, size_t v_stop_2053_, lean_object* v_b_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_usize_dec_eq(v_i_2052_, v_stop_2053_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; 
v___x_2056_ = lean_array_uget_borrowed(v_as_2051_, v_i_2052_);
lean_inc(v___x_2056_);
v___x_2057_ = l_Lean_PersistentArray_push___redArg(v_b_2054_, v___x_2056_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2051_ = stack[0].m_obj;
size_t v_i_2052_ = stack[1].m_num;
size_t v_stop_2053_ = stack[2].m_num;
lean_object* v_b_2054_ = stack[3].m_obj;
lean_object* v_res_2061_;
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2051_, v_i_2052_, v_stop_2053_, v_b_2054_);
stack->m_obj
 = v_res_2061_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2062_, lean_object* v_i_2063_, lean_object* v_stop_2064_, lean_object* v_b_2065_){
_start:
{
size_t v_i_boxed_2066_; size_t v_stop_boxed_2067_; lean_object* v_res_2068_; 
v_i_boxed_2066_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_stop_boxed_2067_ = lean_unbox_usize(v_stop_2064_);
lean_dec(v_stop_2064_);
v_res_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2062_, v_i_boxed_2066_, v_stop_boxed_2067_, v_b_2065_);
lean_dec_ref(v_as_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
lean_object* v_cs_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_cs_2071_ = lean_ctor_get(v_x_2069_, 0);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_array_get_size(v_cs_2071_);
v___x_2074_ = lean_nat_dec_lt(v___x_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
return v_x_2070_;
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_of_nat(v___x_2073_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2071_, v___x_2075_, v___x_2076_, v_x_2070_);
return v___x_2077_;
}
}
else
{
lean_object* v_vs_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_vs_2078_ = lean_ctor_get(v_x_2069_, 0);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_array_get_size(v_vs_2078_);
v___x_2081_ = lean_nat_dec_lt(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
return v_x_2070_;
}
else
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2080_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2078_, v___x_2082_, v___x_2083_, v_x_2070_);
return v___x_2084_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2085_, size_t v_i_2086_, size_t v_stop_2087_, lean_object* v_b_2088_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_usize_dec_eq(v_i_2086_, v_stop_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; 
v___x_2090_ = lean_array_uget_borrowed(v_as_2085_, v_i_2086_);
v___x_2091_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2090_, v_b_2088_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2086_, v___x_2092_);
v_i_2086_ = v___x_2093_;
v_b_2088_ = v___x_2091_;
goto _start;
}
else
{
return v_b_2088_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2085_ = stack[0].m_obj;
size_t v_i_2086_ = stack[1].m_num;
size_t v_stop_2087_ = stack[2].m_num;
lean_object* v_b_2088_ = stack[3].m_obj;
lean_object* v_res_2095_;
v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2085_, v_i_2086_, v_stop_2087_, v_b_2088_);
stack->m_obj
 = v_res_2095_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2096_, lean_object* v_i_2097_, lean_object* v_stop_2098_, lean_object* v_b_2099_){
_start:
{
size_t v_i_boxed_2100_; size_t v_stop_boxed_2101_; lean_object* v_res_2102_; 
v_i_boxed_2100_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_stop_boxed_2101_ = lean_unbox_usize(v_stop_2098_);
lean_dec(v_stop_2098_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2096_, v_i_boxed_2100_, v_stop_boxed_2101_, v_b_2099_);
lean_dec_ref(v_as_2096_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2103_, v_x_2104_);
lean_dec_ref(v_x_2103_);
return v_res_2105_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2106_, size_t v_x_2107_, size_t v_x_2108_, lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2106_) == 0)
{
lean_object* v_cs_2110_; lean_object* v___x_2111_; size_t v___x_2112_; lean_object* v_j_2113_; lean_object* v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_cs_2110_ = lean_ctor_get(v_x_2106_, 0);
v___x_2111_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2112_ = lean_usize_shift_right(v_x_2107_, v_x_2108_);
v_j_2113_ = lean_usize_to_nat(v___x_2112_);
v___x_2114_ = lean_array_get_borrowed(v___x_2111_, v_cs_2110_, v_j_2113_);
v___x_2115_ = ((size_t)1ULL);
v___x_2116_ = lean_usize_shift_left(v___x_2115_, v_x_2108_);
v___x_2117_ = lean_usize_sub(v___x_2116_, v___x_2115_);
v___x_2118_ = lean_usize_land(v_x_2107_, v___x_2117_);
v___x_2119_ = ((size_t)5ULL);
v___x_2120_ = lean_usize_sub(v_x_2108_, v___x_2119_);
v___x_2121_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2114_, v___x_2118_, v___x_2120_, v_x_2109_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_add(v_j_2113_, v___x_2122_);
lean_dec(v_j_2113_);
v___x_2124_ = lean_array_get_size(v_cs_2110_);
v___x_2125_ = lean_nat_dec_lt(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec(v___x_2123_);
return v___x_2121_;
}
else
{
size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = lean_usize_of_nat(v___x_2123_);
lean_dec(v___x_2123_);
v___x_2127_ = lean_usize_of_nat(v___x_2124_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2110_, v___x_2126_, v___x_2127_, v___x_2121_);
return v___x_2128_;
}
}
else
{
lean_object* v_vs_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_vs_2129_ = lean_ctor_get(v_x_2106_, 0);
v___x_2130_ = lean_usize_to_nat(v_x_2107_);
v___x_2131_ = lean_array_get_size(v_vs_2129_);
v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_dec(v___x_2130_);
return v_x_2109_;
}
else
{
size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_usize_of_nat(v___x_2130_);
lean_dec(v___x_2130_);
v___x_2134_ = lean_usize_of_nat(v___x_2131_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2129_, v___x_2133_, v___x_2134_, v_x_2109_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2106_ = stack[0].m_obj;
size_t v_x_2107_ = stack[1].m_num;
size_t v_x_2108_ = stack[2].m_num;
lean_object* v_x_2109_ = stack[3].m_obj;
lean_object* v_res_2136_;
v_res_2136_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2106_, v_x_2107_, v_x_2108_, v_x_2109_);
stack->m_obj
 = v_res_2136_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
size_t v_x_1155__boxed_2141_; size_t v_x_1156__boxed_2142_; lean_object* v_res_2143_; 
v_x_1155__boxed_2141_ = lean_unbox_usize(v_x_2138_);
lean_dec(v_x_2138_);
v_x_1156__boxed_2142_ = lean_unbox_usize(v_x_2139_);
lean_dec(v_x_2139_);
v_res_2143_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2137_, v_x_1155__boxed_2141_, v_x_1156__boxed_2142_, v_x_2140_);
lean_dec_ref(v_x_2137_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2144_, lean_object* v_init_2145_, lean_object* v_start_2146_){
_start:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_nat_dec_eq(v_start_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v_root_2149_; lean_object* v_tail_2150_; size_t v_shift_2151_; lean_object* v_tailOff_2152_; uint8_t v___x_2153_; 
v_root_2149_ = lean_ctor_get(v_t_2144_, 0);
v_tail_2150_ = lean_ctor_get(v_t_2144_, 1);
v_shift_2151_ = lean_ctor_get_usize(v_t_2144_, 4);
v_tailOff_2152_ = lean_ctor_get(v_t_2144_, 3);
v___x_2153_ = lean_nat_dec_le(v_tailOff_2152_, v_start_2146_);
if (v___x_2153_ == 0)
{
size_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2154_ = lean_usize_of_nat(v_start_2146_);
v___x_2155_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2149_, v___x_2154_, v_shift_2151_, v_init_2145_);
v___x_2156_ = lean_array_get_size(v_tail_2150_);
v___x_2157_ = lean_nat_dec_lt(v___x_2147_, v___x_2156_);
if (v___x_2157_ == 0)
{
return v___x_2155_;
}
else
{
size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = lean_usize_of_nat(v___x_2156_);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2150_, v___x_2158_, v___x_2159_, v___x_2155_);
return v___x_2160_;
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2161_ = lean_nat_sub(v_start_2146_, v_tailOff_2152_);
v___x_2162_ = lean_array_get_size(v_tail_2150_);
v___x_2163_ = lean_nat_dec_lt(v___x_2161_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_dec(v___x_2161_);
return v_init_2145_;
}
else
{
size_t v___x_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_usize_of_nat(v___x_2161_);
lean_dec(v___x_2161_);
v___x_2165_ = lean_usize_of_nat(v___x_2162_);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2150_, v___x_2164_, v___x_2165_, v_init_2145_);
return v___x_2166_;
}
}
}
else
{
lean_object* v_root_2167_; lean_object* v_tail_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_root_2167_ = lean_ctor_get(v_t_2144_, 0);
v_tail_2168_ = lean_ctor_get(v_t_2144_, 1);
v___x_2169_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2167_, v_init_2145_);
v___x_2170_ = lean_array_get_size(v_tail_2168_);
v___x_2171_ = lean_nat_dec_lt(v___x_2147_, v___x_2170_);
if (v___x_2171_ == 0)
{
return v___x_2169_;
}
else
{
size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = lean_usize_of_nat(v___x_2170_);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2168_, v___x_2172_, v___x_2173_, v___x_2169_);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2175_, lean_object* v_init_2176_, lean_object* v_start_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2175_, v_init_2176_, v_start_2177_);
lean_dec(v_start_2177_);
lean_dec_ref(v_t_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2179_, lean_object* v_t_u2082_2180_){
_start:
{
uint8_t v___x_2181_; 
v___x_2181_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2179_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2180_, v_t_u2081_2179_, v___x_2182_);
return v___x_2183_;
}
else
{
lean_dec_ref(v_t_u2081_2179_);
lean_inc_ref(v_t_u2082_2180_);
return v_t_u2082_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2184_, lean_object* v_t_u2082_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2184_, v_t_u2082_2185_);
lean_dec_ref(v_t_u2082_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2187_, lean_object* v_t_u2081_2188_, lean_object* v_t_u2082_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2188_, v_t_u2082_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_t_u2081_2192_, lean_object* v_t_u2082_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_PersistentArray_append(v_00_u03b1_2191_, v_t_u2081_2192_, v_t_u2082_2193_);
lean_dec_ref(v_t_u2082_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2195_, lean_object* v_t_2196_, lean_object* v_init_2197_, lean_object* v_start_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2196_, v_init_2197_, v_start_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_t_2201_, lean_object* v_init_2202_, lean_object* v_start_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2200_, v_t_2201_, v_init_2202_, v_start_2203_);
lean_dec(v_start_2203_);
lean_dec_ref(v_t_2201_);
return v_res_2204_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2205_, lean_object* v_x_2206_, size_t v_x_2207_, size_t v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2206_, v_x_2207_, v_x_2208_, v_x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2206_ = stack[1].m_obj;
size_t v_x_2207_ = stack[2].m_num;
size_t v_x_2208_ = stack[3].m_num;
lean_object* v_x_2209_ = stack[4].m_obj;
lean_object* v_res_2211_;
v_res_2211_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_box(0), v_x_2206_, v_x_2207_, v_x_2208_, v_x_2209_);
stack->m_obj
 = v_res_2211_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
size_t v_x_1331__boxed_2217_; size_t v_x_1332__boxed_2218_; lean_object* v_res_2219_; 
v_x_1331__boxed_2217_ = lean_unbox_usize(v_x_2214_);
lean_dec(v_x_2214_);
v_x_1332__boxed_2218_ = lean_unbox_usize(v_x_2215_);
lean_dec(v_x_2215_);
v_res_2219_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2212_, v_x_2213_, v_x_1331__boxed_2217_, v_x_1332__boxed_2218_, v_x_2216_);
lean_dec_ref(v_x_2213_);
return v_res_2219_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2220_, lean_object* v_as_2221_, size_t v_i_2222_, size_t v_stop_2223_, lean_object* v_b_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2221_, v_i_2222_, v_stop_2223_, v_b_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2221_ = stack[1].m_obj;
size_t v_i_2222_ = stack[2].m_num;
size_t v_stop_2223_ = stack[3].m_num;
lean_object* v_b_2224_ = stack[4].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_box(0), v_as_2221_, v_i_2222_, v_stop_2223_, v_b_2224_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_as_2228_, lean_object* v_i_2229_, lean_object* v_stop_2230_, lean_object* v_b_2231_){
_start:
{
size_t v_i_boxed_2232_; size_t v_stop_boxed_2233_; lean_object* v_res_2234_; 
v_i_boxed_2232_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_stop_boxed_2233_ = lean_unbox_usize(v_stop_2230_);
lean_dec(v_stop_2230_);
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2227_, v_as_2228_, v_i_boxed_2232_, v_stop_boxed_2233_, v_b_2231_);
lean_dec_ref(v_as_2228_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2236_, v_x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2239_, v_x_2240_, v_x_2241_);
lean_dec_ref(v_x_2240_);
return v_res_2242_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2243_, lean_object* v_as_2244_, size_t v_i_2245_, size_t v_stop_2246_, lean_object* v_b_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2244_, v_i_2245_, v_stop_2246_, v_b_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2244_ = stack[1].m_obj;
size_t v_i_2245_ = stack[2].m_num;
size_t v_stop_2246_ = stack[3].m_num;
lean_object* v_b_2247_ = stack[4].m_obj;
lean_object* v_res_2249_;
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_box(0), v_as_2244_, v_i_2245_, v_stop_2246_, v_b_2247_);
stack->m_obj
 = v_res_2249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2250_, lean_object* v_as_2251_, lean_object* v_i_2252_, lean_object* v_stop_2253_, lean_object* v_b_2254_){
_start:
{
size_t v_i_boxed_2255_; size_t v_stop_boxed_2256_; lean_object* v_res_2257_; 
v_i_boxed_2255_ = lean_unbox_usize(v_i_2252_);
lean_dec(v_i_2252_);
v_stop_boxed_2256_ = lean_unbox_usize(v_stop_2253_);
lean_dec(v_stop_2253_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2250_, v_as_2251_, v_i_boxed_2255_, v_stop_boxed_2256_, v_b_2254_);
lean_dec_ref(v_as_2251_);
return v_res_2257_;
}
}
lean_object* l_Lean_PersistentArray_instAppend___redArg(){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2260_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_instAppend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2261_;
v_res_2261_ = l_Lean_PersistentArray_instAppend___redArg();
stack->m_obj
 = v_res_2261_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg___boxed(lean_object* v___dummy_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_PersistentArray_instAppend___redArg();
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2266_, lean_object* v_x_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_apply_1(v_f_2266_, v_x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2269_, lean_object* v_f_2270_){
_start:
{
lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2271_, 0, v_f_2270_);
v___x_2272_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2273_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2272_, v_t_2269_, v___f_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2274_, lean_object* v_00_u03b2_2275_, lean_object* v_t_2276_, lean_object* v_f_2277_){
_start:
{
lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2278_, 0, v_f_2277_);
v___x_2279_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2280_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2279_, v_t_2276_, v___f_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2281_, lean_object* v_f_2282_){
_start:
{
lean_object* v___f_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2283_, 0, v_f_2282_);
v___x_2284_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2285_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2284_, v_t_2281_, v___f_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_t_2288_, lean_object* v_f_2289_){
_start:
{
lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___f_2290_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2290_, 0, v_f_2289_);
v___x_2291_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2292_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2291_, v_t_2288_, v___f_2290_);
return v___x_2292_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2293_, size_t v_i_2294_, size_t v_stop_2295_, lean_object* v_b_2296_){
_start:
{
uint8_t v___x_2297_; 
v___x_2297_ = lean_usize_dec_eq(v_i_2294_, v_stop_2295_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; 
v___x_2298_ = lean_array_uget_borrowed(v_as_2293_, v_i_2294_);
lean_inc(v___x_2298_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_b_2296_);
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2294_, v___x_2300_);
v_i_2294_ = v___x_2301_;
v_b_2296_ = v___x_2299_;
goto _start;
}
else
{
return v_b_2296_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2293_ = stack[0].m_obj;
size_t v_i_2294_ = stack[1].m_num;
size_t v_stop_2295_ = stack[2].m_num;
lean_object* v_b_2296_ = stack[3].m_obj;
lean_object* v_res_2303_;
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2293_, v_i_2294_, v_stop_2295_, v_b_2296_);
stack->m_obj
 = v_res_2303_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2304_, lean_object* v_i_2305_, lean_object* v_stop_2306_, lean_object* v_b_2307_){
_start:
{
size_t v_i_boxed_2308_; size_t v_stop_boxed_2309_; lean_object* v_res_2310_; 
v_i_boxed_2308_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_stop_boxed_2309_ = lean_unbox_usize(v_stop_2306_);
lean_dec(v_stop_2306_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2304_, v_i_boxed_2308_, v_stop_boxed_2309_, v_b_2307_);
lean_dec_ref(v_as_2304_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
if (lean_obj_tag(v_x_2311_) == 0)
{
lean_object* v_cs_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_cs_2313_ = lean_ctor_get(v_x_2311_, 0);
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = lean_array_get_size(v_cs_2313_);
v___x_2316_ = lean_nat_dec_lt(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
return v_x_2312_;
}
else
{
size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = lean_usize_of_nat(v___x_2315_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2313_, v___x_2317_, v___x_2318_, v_x_2312_);
return v___x_2319_;
}
}
else
{
lean_object* v_vs_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_vs_2320_ = lean_ctor_get(v_x_2311_, 0);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_array_get_size(v_vs_2320_);
v___x_2323_ = lean_nat_dec_lt(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
return v_x_2312_;
}
else
{
size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = lean_usize_of_nat(v___x_2322_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2320_, v___x_2324_, v___x_2325_, v_x_2312_);
return v___x_2326_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2327_, size_t v_i_2328_, size_t v_stop_2329_, lean_object* v_b_2330_){
_start:
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_usize_dec_eq(v_i_2328_, v_stop_2329_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; size_t v___x_2334_; size_t v___x_2335_; 
v___x_2332_ = lean_array_uget_borrowed(v_as_2327_, v_i_2328_);
v___x_2333_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2332_, v_b_2330_);
v___x_2334_ = ((size_t)1ULL);
v___x_2335_ = lean_usize_add(v_i_2328_, v___x_2334_);
v_i_2328_ = v___x_2335_;
v_b_2330_ = v___x_2333_;
goto _start;
}
else
{
return v_b_2330_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2327_ = stack[0].m_obj;
size_t v_i_2328_ = stack[1].m_num;
size_t v_stop_2329_ = stack[2].m_num;
lean_object* v_b_2330_ = stack[3].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2327_, v_i_2328_, v_stop_2329_, v_b_2330_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2338_, lean_object* v_i_2339_, lean_object* v_stop_2340_, lean_object* v_b_2341_){
_start:
{
size_t v_i_boxed_2342_; size_t v_stop_boxed_2343_; lean_object* v_res_2344_; 
v_i_boxed_2342_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_stop_boxed_2343_ = lean_unbox_usize(v_stop_2340_);
lean_dec(v_stop_2340_);
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2338_, v_i_boxed_2342_, v_stop_boxed_2343_, v_b_2341_);
lean_dec_ref(v_as_2338_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2345_, v_x_2346_);
lean_dec_ref(v_x_2345_);
return v_res_2347_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2348_, size_t v_x_2349_, size_t v_x_2350_, lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2348_) == 0)
{
lean_object* v_cs_2352_; lean_object* v___x_2353_; size_t v___x_2354_; lean_object* v_j_2355_; lean_object* v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_cs_2352_ = lean_ctor_get(v_x_2348_, 0);
v___x_2353_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2354_ = lean_usize_shift_right(v_x_2349_, v_x_2350_);
v_j_2355_ = lean_usize_to_nat(v___x_2354_);
v___x_2356_ = lean_array_get_borrowed(v___x_2353_, v_cs_2352_, v_j_2355_);
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_shift_left(v___x_2357_, v_x_2350_);
v___x_2359_ = lean_usize_sub(v___x_2358_, v___x_2357_);
v___x_2360_ = lean_usize_land(v_x_2349_, v___x_2359_);
v___x_2361_ = ((size_t)5ULL);
v___x_2362_ = lean_usize_sub(v_x_2350_, v___x_2361_);
v___x_2363_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2356_, v___x_2360_, v___x_2362_, v_x_2351_);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_j_2355_, v___x_2364_);
lean_dec(v_j_2355_);
v___x_2366_ = lean_array_get_size(v_cs_2352_);
v___x_2367_ = lean_nat_dec_lt(v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_dec(v___x_2365_);
return v___x_2363_;
}
else
{
size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = lean_usize_of_nat(v___x_2365_);
lean_dec(v___x_2365_);
v___x_2369_ = lean_usize_of_nat(v___x_2366_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2352_, v___x_2368_, v___x_2369_, v___x_2363_);
return v___x_2370_;
}
}
else
{
lean_object* v_vs_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_vs_2371_ = lean_ctor_get(v_x_2348_, 0);
v___x_2372_ = lean_usize_to_nat(v_x_2349_);
v___x_2373_ = lean_array_get_size(v_vs_2371_);
v___x_2374_ = lean_nat_dec_lt(v___x_2372_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_dec(v___x_2372_);
return v_x_2351_;
}
else
{
size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_usize_of_nat(v___x_2372_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_usize_of_nat(v___x_2373_);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2371_, v___x_2375_, v___x_2376_, v_x_2351_);
return v___x_2377_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2348_ = stack[0].m_obj;
size_t v_x_2349_ = stack[1].m_num;
size_t v_x_2350_ = stack[2].m_num;
lean_object* v_x_2351_ = stack[3].m_obj;
lean_object* v_res_2378_;
v_res_2378_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2348_, v_x_2349_, v_x_2350_, v_x_2351_);
stack->m_obj
 = v_res_2378_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
size_t v_x_1149__boxed_2383_; size_t v_x_1150__boxed_2384_; lean_object* v_res_2385_; 
v_x_1149__boxed_2383_ = lean_unbox_usize(v_x_2380_);
lean_dec(v_x_2380_);
v_x_1150__boxed_2384_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_res_2385_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2379_, v_x_1149__boxed_2383_, v_x_1150__boxed_2384_, v_x_2382_);
lean_dec_ref(v_x_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2386_, lean_object* v_init_2387_, lean_object* v_start_2388_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_nat_dec_eq(v_start_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v_root_2391_; lean_object* v_tail_2392_; size_t v_shift_2393_; lean_object* v_tailOff_2394_; uint8_t v___x_2395_; 
v_root_2391_ = lean_ctor_get(v_t_2386_, 0);
v_tail_2392_ = lean_ctor_get(v_t_2386_, 1);
v_shift_2393_ = lean_ctor_get_usize(v_t_2386_, 4);
v_tailOff_2394_ = lean_ctor_get(v_t_2386_, 3);
v___x_2395_ = lean_nat_dec_le(v_tailOff_2394_, v_start_2388_);
if (v___x_2395_ == 0)
{
size_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2396_ = lean_usize_of_nat(v_start_2388_);
v___x_2397_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2391_, v___x_2396_, v_shift_2393_, v_init_2387_);
v___x_2398_ = lean_array_get_size(v_tail_2392_);
v___x_2399_ = lean_nat_dec_lt(v___x_2389_, v___x_2398_);
if (v___x_2399_ == 0)
{
return v___x_2397_;
}
else
{
size_t v___x_2400_; size_t v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = ((size_t)0ULL);
v___x_2401_ = lean_usize_of_nat(v___x_2398_);
v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2392_, v___x_2400_, v___x_2401_, v___x_2397_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = lean_nat_sub(v_start_2388_, v_tailOff_2394_);
v___x_2404_ = lean_array_get_size(v_tail_2392_);
v___x_2405_ = lean_nat_dec_lt(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_dec(v___x_2403_);
return v_init_2387_;
}
else
{
size_t v___x_2406_; size_t v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = lean_usize_of_nat(v___x_2403_);
lean_dec(v___x_2403_);
v___x_2407_ = lean_usize_of_nat(v___x_2404_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2392_, v___x_2406_, v___x_2407_, v_init_2387_);
return v___x_2408_;
}
}
}
else
{
lean_object* v_root_2409_; lean_object* v_tail_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_root_2409_ = lean_ctor_get(v_t_2386_, 0);
v_tail_2410_ = lean_ctor_get(v_t_2386_, 1);
v___x_2411_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2409_, v_init_2387_);
v___x_2412_ = lean_array_get_size(v_tail_2410_);
v___x_2413_ = lean_nat_dec_lt(v___x_2389_, v___x_2412_);
if (v___x_2413_ == 0)
{
return v___x_2411_;
}
else
{
size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((size_t)0ULL);
v___x_2415_ = lean_usize_of_nat(v___x_2412_);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2410_, v___x_2414_, v___x_2415_, v___x_2411_);
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2417_, lean_object* v_init_2418_, lean_object* v_start_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2417_, v_init_2418_, v_start_2419_);
lean_dec(v_start_2419_);
lean_dec_ref(v_t_2417_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2421_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2421_, v___x_2422_, v___x_2423_);
v___x_2425_ = l_List_reverse___redArg(v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_PersistentArray_toList___redArg(v_t_2426_);
lean_dec_ref(v_t_2426_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2428_, lean_object* v_t_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_PersistentArray_toList___redArg(v_t_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_t_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_PersistentArray_toList(v_00_u03b1_2431_, v_t_2432_);
lean_dec_ref(v_t_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2434_, lean_object* v_t_2435_, lean_object* v_init_2436_, lean_object* v_start_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2435_, v_init_2436_, v_start_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2439_, lean_object* v_t_2440_, lean_object* v_init_2441_, lean_object* v_start_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2439_, v_t_2440_, v_init_2441_, v_start_2442_);
lean_dec(v_start_2442_);
lean_dec_ref(v_t_2440_);
return v_res_2443_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2444_, lean_object* v_x_2445_, size_t v_x_2446_, size_t v_x_2447_, lean_object* v_x_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2445_, v_x_2446_, v_x_2447_, v_x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2445_ = stack[1].m_obj;
size_t v_x_2446_ = stack[2].m_num;
size_t v_x_2447_ = stack[3].m_num;
lean_object* v_x_2448_ = stack[4].m_obj;
lean_object* v_res_2450_;
v_res_2450_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_box(0), v_x_2445_, v_x_2446_, v_x_2447_, v_x_2448_);
stack->m_obj
 = v_res_2450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_){
_start:
{
size_t v_x_1328__boxed_2456_; size_t v_x_1329__boxed_2457_; lean_object* v_res_2458_; 
v_x_1328__boxed_2456_ = lean_unbox_usize(v_x_2453_);
lean_dec(v_x_2453_);
v_x_1329__boxed_2457_ = lean_unbox_usize(v_x_2454_);
lean_dec(v_x_2454_);
v_res_2458_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2451_, v_x_2452_, v_x_1328__boxed_2456_, v_x_1329__boxed_2457_, v_x_2455_);
lean_dec_ref(v_x_2452_);
return v_res_2458_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2459_, lean_object* v_as_2460_, size_t v_i_2461_, size_t v_stop_2462_, lean_object* v_b_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2460_, v_i_2461_, v_stop_2462_, v_b_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2460_ = stack[1].m_obj;
size_t v_i_2461_ = stack[2].m_num;
size_t v_stop_2462_ = stack[3].m_num;
lean_object* v_b_2463_ = stack[4].m_obj;
lean_object* v_res_2465_;
v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_box(0), v_as_2460_, v_i_2461_, v_stop_2462_, v_b_2463_);
stack->m_obj
 = v_res_2465_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_as_2467_, lean_object* v_i_2468_, lean_object* v_stop_2469_, lean_object* v_b_2470_){
_start:
{
size_t v_i_boxed_2471_; size_t v_stop_boxed_2472_; lean_object* v_res_2473_; 
v_i_boxed_2471_ = lean_unbox_usize(v_i_2468_);
lean_dec(v_i_2468_);
v_stop_boxed_2472_ = lean_unbox_usize(v_stop_2469_);
lean_dec(v_stop_2469_);
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2466_, v_as_2467_, v_i_boxed_2471_, v_stop_boxed_2472_, v_b_2470_);
lean_dec_ref(v_as_2467_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2474_, lean_object* v_x_2475_, lean_object* v_x_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2475_, v_x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2478_, v_x_2479_, v_x_2480_);
lean_dec_ref(v_x_2479_);
return v_res_2481_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2482_, lean_object* v_as_2483_, size_t v_i_2484_, size_t v_stop_2485_, lean_object* v_b_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2483_, v_i_2484_, v_stop_2485_, v_b_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2483_ = stack[1].m_obj;
size_t v_i_2484_ = stack[2].m_num;
size_t v_stop_2485_ = stack[3].m_num;
lean_object* v_b_2486_ = stack[4].m_obj;
lean_object* v_res_2488_;
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_box(0), v_as_2483_, v_i_2484_, v_stop_2485_, v_b_2486_);
stack->m_obj
 = v_res_2488_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_as_2490_, lean_object* v_i_2491_, lean_object* v_stop_2492_, lean_object* v_b_2493_){
_start:
{
size_t v_i_boxed_2494_; size_t v_stop_boxed_2495_; lean_object* v_res_2496_; 
v_i_boxed_2494_ = lean_unbox_usize(v_i_2491_);
lean_dec(v_i_2491_);
v_stop_boxed_2495_ = lean_unbox_usize(v_stop_2492_);
lean_dec(v_stop_2492_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2489_, v_as_2490_, v_i_boxed_2494_, v_stop_boxed_2495_, v_b_2493_);
lean_dec_ref(v_as_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2497_, lean_object* v_p_2498_, lean_object* v_x_2499_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
lean_object* v_toApplicative_2500_; lean_object* v_cs_2501_; lean_object* v_toPure_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v_toApplicative_2500_ = lean_ctor_get(v_inst_2497_, 0);
v_cs_2501_ = lean_ctor_get(v_x_2499_, 0);
lean_inc_ref(v_cs_2501_);
lean_dec_ref_known(v_x_2499_, 1);
v_toPure_2502_ = lean_ctor_get(v_toApplicative_2500_, 1);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = lean_array_get_size(v_cs_2501_);
v___x_2505_ = lean_nat_dec_lt(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_inc(v_toPure_2502_);
lean_dec_ref(v_cs_2501_);
lean_dec(v_p_2498_);
lean_dec_ref(v_inst_2497_);
v___x_2506_ = lean_box(v___x_2505_);
v___x_2507_ = lean_apply_2(v_toPure_2502_, lean_box(0), v___x_2506_);
return v___x_2507_;
}
else
{
if (v___x_2505_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_inc(v_toPure_2502_);
lean_dec_ref(v_cs_2501_);
lean_dec(v_p_2498_);
lean_dec_ref(v_inst_2497_);
v___x_2508_ = lean_box(v___x_2505_);
v___x_2509_ = lean_apply_2(v_toPure_2502_, lean_box(0), v___x_2508_);
return v___x_2509_;
}
else
{
lean_object* v___f_2510_; size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
lean_inc_ref(v_inst_2497_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2510_, 0, v_inst_2497_);
lean_closure_set(v___f_2510_, 1, v_p_2498_);
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = lean_usize_of_nat(v___x_2504_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2497_, v___f_2510_, v_cs_2501_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
}
else
{
lean_object* v_toApplicative_2514_; lean_object* v_vs_2515_; lean_object* v_toPure_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_toApplicative_2514_ = lean_ctor_get(v_inst_2497_, 0);
v_vs_2515_ = lean_ctor_get(v_x_2499_, 0);
lean_inc_ref(v_vs_2515_);
lean_dec_ref_known(v_x_2499_, 1);
v_toPure_2516_ = lean_ctor_get(v_toApplicative_2514_, 1);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v_vs_2515_);
v___x_2519_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_inc(v_toPure_2516_);
lean_dec_ref(v_vs_2515_);
lean_dec(v_p_2498_);
lean_dec_ref(v_inst_2497_);
v___x_2520_ = lean_box(v___x_2519_);
v___x_2521_ = lean_apply_2(v_toPure_2516_, lean_box(0), v___x_2520_);
return v___x_2521_;
}
else
{
if (v___x_2519_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_inc(v_toPure_2516_);
lean_dec_ref(v_vs_2515_);
lean_dec(v_p_2498_);
lean_dec_ref(v_inst_2497_);
v___x_2522_ = lean_box(v___x_2519_);
v___x_2523_ = lean_apply_2(v_toPure_2516_, lean_box(0), v___x_2522_);
return v___x_2523_;
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2518_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2497_, v_p_2498_, v_vs_2515_, v___x_2524_, v___x_2525_);
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2527_, lean_object* v_p_2528_, lean_object* v_c_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2527_, v_p_2528_, v_c_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2531_, lean_object* v_m_2532_, lean_object* v_inst_2533_, lean_object* v_p_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2533_, v_p_2534_, v_x_2535_);
return v___x_2536_;
}
}
lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2537_, lean_object* v_toPure_2538_, lean_object* v_inst_2539_, lean_object* v_p_2540_, uint8_t v_b_2541_){
_start:
{
if (v_b_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_array_get_size(v_tail_2537_);
v___x_2544_ = lean_nat_dec_lt(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v_p_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec_ref(v_tail_2537_);
v___x_2545_ = lean_box(v___x_2544_);
v___x_2546_ = lean_apply_2(v_toPure_2538_, lean_box(0), v___x_2545_);
return v___x_2546_;
}
else
{
if (v___x_2544_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_p_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec_ref(v_tail_2537_);
v___x_2547_ = lean_box(v___x_2544_);
v___x_2548_ = lean_apply_2(v_toPure_2538_, lean_box(0), v___x_2547_);
return v___x_2548_;
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_toPure_2538_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2543_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2539_, v_p_2540_, v_tail_2537_, v___x_2549_, v___x_2550_);
return v___x_2551_;
}
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_p_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec_ref(v_tail_2537_);
v___x_2552_ = lean_box(v_b_2541_);
v___x_2553_ = lean_apply_2(v_toPure_2538_, lean_box(0), v___x_2552_);
return v___x_2553_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_2537_ = stack[0].m_obj;
lean_object* v_toPure_2538_ = stack[1].m_obj;
lean_object* v_inst_2539_ = stack[2].m_obj;
lean_object* v_p_2540_ = stack[3].m_obj;
uint8_t v_b_2541_ = stack[4].m_num;
lean_object* v_res_2554_;
v_res_2554_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2537_, v_toPure_2538_, v_inst_2539_, v_p_2540_, v_b_2541_);
stack->m_obj
 = v_res_2554_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2555_, lean_object* v_toPure_2556_, lean_object* v_inst_2557_, lean_object* v_p_2558_, lean_object* v_b_2559_){
_start:
{
uint8_t v_b_boxed_2560_; lean_object* v_res_2561_; 
v_b_boxed_2560_ = lean_unbox(v_b_2559_);
v_res_2561_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2555_, v_toPure_2556_, v_inst_2557_, v_p_2558_, v_b_boxed_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2562_, lean_object* v_t_2563_, lean_object* v_p_2564_){
_start:
{
lean_object* v_toApplicative_2565_; lean_object* v_toBind_2566_; lean_object* v_root_2567_; lean_object* v_tail_2568_; lean_object* v_toPure_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; 
v_toApplicative_2565_ = lean_ctor_get(v_inst_2562_, 0);
v_toBind_2566_ = lean_ctor_get(v_inst_2562_, 1);
lean_inc(v_toBind_2566_);
v_root_2567_ = lean_ctor_get(v_t_2563_, 0);
lean_inc_ref(v_root_2567_);
v_tail_2568_ = lean_ctor_get(v_t_2563_, 1);
lean_inc_ref(v_tail_2568_);
lean_dec_ref(v_t_2563_);
v_toPure_2569_ = lean_ctor_get(v_toApplicative_2565_, 1);
lean_inc(v_toPure_2569_);
lean_inc(v_p_2564_);
lean_inc_ref(v_inst_2562_);
v___x_2570_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2562_, v_p_2564_, v_root_2567_);
v___f_2571_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2571_, 0, v_tail_2568_);
lean_closure_set(v___f_2571_, 1, v_toPure_2569_);
lean_closure_set(v___f_2571_, 2, v_inst_2562_);
lean_closure_set(v___f_2571_, 3, v_p_2564_);
v___x_2572_ = lean_apply_4(v_toBind_2566_, lean_box(0), lean_box(0), v___x_2570_, v___f_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2573_, lean_object* v_m_2574_, lean_object* v_inst_2575_, lean_object* v_t_2576_, lean_object* v_p_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2575_, v_t_2576_, v_p_2577_);
return v___x_2578_;
}
}
lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2579_, uint8_t v_b_2580_){
_start:
{
if (v_b_2580_ == 0)
{
uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = 1;
v___x_2582_ = lean_box(v___x_2581_);
v___x_2583_ = lean_apply_2(v_toPure_2579_, lean_box(0), v___x_2582_);
return v___x_2583_;
}
else
{
uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = 0;
v___x_2585_ = lean_box(v___x_2584_);
v___x_2586_ = lean_apply_2(v_toPure_2579_, lean_box(0), v___x_2585_);
return v___x_2586_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_allM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2579_ = stack[0].m_obj;
uint8_t v_b_2580_ = stack[1].m_num;
lean_object* v_res_2587_;
v_res_2587_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2579_, v_b_2580_);
stack->m_obj
 = v_res_2587_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2588_, lean_object* v_b_2589_){
_start:
{
uint8_t v_b_boxed_2590_; lean_object* v_res_2591_; 
v_b_boxed_2590_ = lean_unbox(v_b_2589_);
v_res_2591_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2588_, v_b_boxed_2590_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2592_, lean_object* v_toBind_2593_, lean_object* v___f_2594_, lean_object* v_v_2595_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_apply_1(v_p_2592_, v_v_2595_);
v___x_2597_ = lean_apply_4(v_toBind_2593_, lean_box(0), lean_box(0), v___x_2596_, v___f_2594_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2598_, lean_object* v_a_2599_, lean_object* v_p_2600_){
_start:
{
lean_object* v_toApplicative_2601_; lean_object* v_toBind_2602_; lean_object* v_toPure_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_toApplicative_2601_ = lean_ctor_get(v_inst_2598_, 0);
v_toBind_2602_ = lean_ctor_get(v_inst_2598_, 1);
lean_inc_n(v_toBind_2602_, 2);
v_toPure_2603_ = lean_ctor_get(v_toApplicative_2601_, 1);
lean_inc(v_toPure_2603_);
v___f_2604_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2604_, 0, v_toPure_2603_);
lean_inc_ref(v___f_2604_);
v___f_2605_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2605_, 0, v_p_2600_);
lean_closure_set(v___f_2605_, 1, v_toBind_2602_);
lean_closure_set(v___f_2605_, 2, v___f_2604_);
v___x_2606_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2598_, v_a_2599_, v___f_2605_);
v___x_2607_ = lean_apply_4(v_toBind_2602_, lean_box(0), lean_box(0), v___x_2606_, v___f_2604_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2608_, lean_object* v_m_2609_, lean_object* v_inst_2610_, lean_object* v_a_2611_, lean_object* v_p_2612_){
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
uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2620_, lean_object* v_x_2621_){
_start:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = lean_apply_1(v_p_2620_, v_x_2621_);
v___x_2623_ = lean_unbox(v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2620_ = stack[0].m_obj;
lean_object* v_x_2621_ = stack[1].m_obj;
uint8_t v_res_2624_;
v_res_2624_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2620_, v_x_2621_);
stack->m_num = v_res_2624_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2625_, lean_object* v_x_2626_){
_start:
{
uint8_t v_res_2627_; lean_object* v_r_2628_; 
v_res_2627_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2625_, v_x_2626_);
v_r_2628_ = lean_box(v_res_2627_);
return v_r_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg(lean_object* v_a_2629_, lean_object* v_p_2630_){
_start:
{
lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2631_, 0, v_p_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2633_ = l_Lean_PersistentArray_anyM___redArg(v___x_2632_, v_a_2629_, v___f_2631_);
return v___x_2633_;
}
}
uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2634_, lean_object* v_a_2635_, lean_object* v_p_2636_){
_start:
{
lean_object* v___f_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___f_2637_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2637_, 0, v_p_2636_);
v___x_2638_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2639_ = l_Lean_PersistentArray_anyM___redArg(v___x_2638_, v_a_2635_, v___f_2637_);
v___x_2640_ = lean_unbox(v___x_2639_);
lean_dec(v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2635_ = stack[1].m_obj;
lean_object* v_p_2636_ = stack[2].m_obj;
uint8_t v_res_2641_;
v_res_2641_ = l_Lean_PersistentArray_any(lean_box(0), v_a_2635_, v_p_2636_);
stack->m_num = v_res_2641_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_a_2643_, lean_object* v_p_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Lean_PersistentArray_any(v_00_u03b1_2642_, v_a_2643_, v_p_2644_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2647_, lean_object* v_x_2648_){
_start:
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = lean_apply_1(v_p_2647_, v_x_2648_);
v___x_2650_ = lean_unbox(v___x_2649_);
if (v___x_2650_ == 0)
{
uint8_t v___x_2651_; 
v___x_2651_ = 1;
return v___x_2651_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = 0;
return v___x_2652_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2647_ = stack[0].m_obj;
lean_object* v_x_2648_ = stack[1].m_obj;
uint8_t v_res_2653_;
v_res_2653_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2647_, v_x_2648_);
stack->m_num = v_res_2653_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2654_, lean_object* v_x_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2654_, v_x_2655_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2658_, lean_object* v_p_2659_){
_start:
{
lean_object* v___f_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2660_, 0, v_p_2659_);
v___x_2661_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2662_ = l_Lean_PersistentArray_anyM___redArg(v___x_2661_, v_a_2658_, v___f_2660_);
v___x_2663_ = lean_unbox(v___x_2662_);
lean_dec(v___x_2662_);
if (v___x_2663_ == 0)
{
uint8_t v___x_2664_; 
v___x_2664_ = 1;
return v___x_2664_;
}
else
{
uint8_t v___x_2665_; 
v___x_2665_ = 0;
return v___x_2665_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2658_ = stack[0].m_obj;
lean_object* v_p_2659_ = stack[1].m_obj;
uint8_t v_res_2666_;
v_res_2666_ = l_Lean_PersistentArray_all___redArg(v_a_2658_, v_p_2659_);
stack->m_num = v_res_2666_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2667_, lean_object* v_p_2668_){
_start:
{
uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Lean_PersistentArray_all___redArg(v_a_2667_, v_p_2668_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2671_, lean_object* v_a_2672_, lean_object* v_p_2673_){
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
LEAN_EXPORT void l_Lean_PersistentArray_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2672_ = stack[1].m_obj;
lean_object* v_p_2673_ = stack[2].m_obj;
uint8_t v_res_2680_;
v_res_2680_ = l_Lean_PersistentArray_all(lean_box(0), v_a_2672_, v_p_2673_);
stack->m_num = v_res_2680_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2681_, lean_object* v_a_2682_, lean_object* v_p_2683_){
_start:
{
uint8_t v_res_2684_; lean_object* v_r_2685_; 
v_res_2684_ = l_Lean_PersistentArray_all(v_00_u03b1_2681_, v_a_2682_, v_p_2683_);
v_r_2685_ = lean_box(v_res_2684_);
return v_r_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2686_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_cs_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_vs_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2692_, lean_object* v_f_2693_, lean_object* v_x_2694_){
_start:
{
if (lean_obj_tag(v_x_2694_) == 0)
{
lean_object* v_toApplicative_2695_; lean_object* v_toFunctor_2696_; lean_object* v_cs_2697_; lean_object* v_map_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; size_t v_sz_2701_; size_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_toApplicative_2695_ = lean_ctor_get(v_inst_2692_, 0);
v_toFunctor_2696_ = lean_ctor_get(v_toApplicative_2695_, 0);
v_cs_2697_ = lean_ctor_get(v_x_2694_, 0);
lean_inc_ref(v_cs_2697_);
lean_dec_ref_known(v_x_2694_, 1);
v_map_2698_ = lean_ctor_get(v_toFunctor_2696_, 0);
lean_inc(v_map_2698_);
v___f_2699_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2692_);
v___f_2700_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2700_, 0, v_inst_2692_);
lean_closure_set(v___f_2700_, 1, v_f_2693_);
v_sz_2701_ = lean_array_size(v_cs_2697_);
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2692_, v___f_2700_, v_sz_2701_, v___x_2702_, v_cs_2697_);
v___x_2704_ = lean_apply_4(v_map_2698_, lean_box(0), lean_box(0), v___f_2699_, v___x_2703_);
return v___x_2704_;
}
else
{
lean_object* v_toApplicative_2705_; lean_object* v_toFunctor_2706_; lean_object* v_vs_2707_; lean_object* v_map_2708_; lean_object* v___f_2709_; size_t v_sz_2710_; size_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_toApplicative_2705_ = lean_ctor_get(v_inst_2692_, 0);
v_toFunctor_2706_ = lean_ctor_get(v_toApplicative_2705_, 0);
v_vs_2707_ = lean_ctor_get(v_x_2694_, 0);
lean_inc_ref(v_vs_2707_);
lean_dec_ref_known(v_x_2694_, 1);
v_map_2708_ = lean_ctor_get(v_toFunctor_2706_, 0);
lean_inc(v_map_2708_);
v___f_2709_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2710_ = lean_array_size(v_vs_2707_);
v___x_2711_ = ((size_t)0ULL);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2692_, v_f_2693_, v_sz_2710_, v___x_2711_, v_vs_2707_);
v___x_2713_ = lean_apply_4(v_map_2708_, lean_box(0), lean_box(0), v___f_2709_, v___x_2712_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2714_, lean_object* v_f_2715_, lean_object* v_c_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2714_, v_f_2715_, v_c_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2718_, lean_object* v_m_2719_, lean_object* v_inst_2720_, lean_object* v_00_u03b2_2721_, lean_object* v_f_2722_, lean_object* v_x_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2720_, v_f_2722_, v_x_2723_);
return v___x_2724_;
}
}
lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2725_, lean_object* v_size_2726_, size_t v_shift_2727_, lean_object* v_tailOff_2728_, lean_object* v_toPure_2729_, lean_object* v_tail_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2731_, 0, v_root_2725_);
lean_ctor_set(v___x_2731_, 1, v_tail_2730_);
lean_ctor_set(v___x_2731_, 2, v_size_2726_);
lean_ctor_set(v___x_2731_, 3, v_tailOff_2728_);
lean_ctor_set_usize(v___x_2731_, 4, v_shift_2727_);
v___x_2732_ = lean_apply_2(v_toPure_2729_, lean_box(0), v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_2725_ = stack[0].m_obj;
lean_object* v_size_2726_ = stack[1].m_obj;
size_t v_shift_2727_ = stack[2].m_num;
lean_object* v_tailOff_2728_ = stack[3].m_obj;
lean_object* v_toPure_2729_ = stack[4].m_obj;
lean_object* v_tail_2730_ = stack[5].m_obj;
lean_object* v_res_2733_;
v_res_2733_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2725_, v_size_2726_, v_shift_2727_, v_tailOff_2728_, v_toPure_2729_, v_tail_2730_);
stack->m_obj
 = v_res_2733_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2734_, lean_object* v_size_2735_, lean_object* v_shift_2736_, lean_object* v_tailOff_2737_, lean_object* v_toPure_2738_, lean_object* v_tail_2739_){
_start:
{
size_t v_shift_boxed_2740_; lean_object* v_res_2741_; 
v_shift_boxed_2740_ = lean_unbox_usize(v_shift_2736_);
lean_dec(v_shift_2736_);
v_res_2741_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2734_, v_size_2735_, v_shift_boxed_2740_, v_tailOff_2737_, v_toPure_2738_, v_tail_2739_);
return v_res_2741_;
}
}
lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2742_, size_t v_shift_2743_, lean_object* v_tailOff_2744_, lean_object* v_toPure_2745_, lean_object* v_tail_2746_, lean_object* v_inst_2747_, lean_object* v_f_2748_, lean_object* v_toBind_2749_, lean_object* v_root_2750_){
_start:
{
lean_object* v___x_2751_; lean_object* v___f_2752_; size_t v_sz_2753_; size_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2751_ = lean_box_usize(v_shift_2743_);
v___f_2752_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2752_, 0, v_root_2750_);
lean_closure_set(v___f_2752_, 1, v_size_2742_);
lean_closure_set(v___f_2752_, 2, v___x_2751_);
lean_closure_set(v___f_2752_, 3, v_tailOff_2744_);
lean_closure_set(v___f_2752_, 4, v_toPure_2745_);
v_sz_2753_ = lean_array_size(v_tail_2746_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2747_, v_f_2748_, v_sz_2753_, v___x_2754_, v_tail_2746_);
v___x_2756_ = lean_apply_4(v_toBind_2749_, lean_box(0), lean_box(0), v___x_2755_, v___f_2752_);
return v___x_2756_;
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_2742_ = stack[0].m_obj;
size_t v_shift_2743_ = stack[1].m_num;
lean_object* v_tailOff_2744_ = stack[2].m_obj;
lean_object* v_toPure_2745_ = stack[3].m_obj;
lean_object* v_tail_2746_ = stack[4].m_obj;
lean_object* v_inst_2747_ = stack[5].m_obj;
lean_object* v_f_2748_ = stack[6].m_obj;
lean_object* v_toBind_2749_ = stack[7].m_obj;
lean_object* v_root_2750_ = stack[8].m_obj;
lean_object* v_res_2757_;
v_res_2757_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2742_, v_shift_2743_, v_tailOff_2744_, v_toPure_2745_, v_tail_2746_, v_inst_2747_, v_f_2748_, v_toBind_2749_, v_root_2750_);
stack->m_obj
 = v_res_2757_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2758_, lean_object* v_shift_2759_, lean_object* v_tailOff_2760_, lean_object* v_toPure_2761_, lean_object* v_tail_2762_, lean_object* v_inst_2763_, lean_object* v_f_2764_, lean_object* v_toBind_2765_, lean_object* v_root_2766_){
_start:
{
size_t v_shift_boxed_2767_; lean_object* v_res_2768_; 
v_shift_boxed_2767_ = lean_unbox_usize(v_shift_2759_);
lean_dec(v_shift_2759_);
v_res_2768_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2758_, v_shift_boxed_2767_, v_tailOff_2760_, v_toPure_2761_, v_tail_2762_, v_inst_2763_, v_f_2764_, v_toBind_2765_, v_root_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2769_, lean_object* v_f_2770_, lean_object* v_t_2771_){
_start:
{
lean_object* v_toApplicative_2772_; lean_object* v_toBind_2773_; lean_object* v_root_2774_; lean_object* v_tail_2775_; lean_object* v_size_2776_; size_t v_shift_2777_; lean_object* v_tailOff_2778_; lean_object* v_toPure_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; 
v_toApplicative_2772_ = lean_ctor_get(v_inst_2769_, 0);
v_toBind_2773_ = lean_ctor_get(v_inst_2769_, 1);
lean_inc_n(v_toBind_2773_, 2);
v_root_2774_ = lean_ctor_get(v_t_2771_, 0);
lean_inc_ref(v_root_2774_);
v_tail_2775_ = lean_ctor_get(v_t_2771_, 1);
lean_inc_ref(v_tail_2775_);
v_size_2776_ = lean_ctor_get(v_t_2771_, 2);
lean_inc(v_size_2776_);
v_shift_2777_ = lean_ctor_get_usize(v_t_2771_, 4);
v_tailOff_2778_ = lean_ctor_get(v_t_2771_, 3);
lean_inc(v_tailOff_2778_);
lean_dec_ref(v_t_2771_);
v_toPure_2779_ = lean_ctor_get(v_toApplicative_2772_, 1);
lean_inc(v_toPure_2779_);
lean_inc(v_f_2770_);
lean_inc_ref(v_inst_2769_);
v___x_2780_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2769_, v_f_2770_, v_root_2774_);
v___x_2781_ = lean_box_usize(v_shift_2777_);
v___f_2782_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2782_, 0, v_size_2776_);
lean_closure_set(v___f_2782_, 1, v___x_2781_);
lean_closure_set(v___f_2782_, 2, v_tailOff_2778_);
lean_closure_set(v___f_2782_, 3, v_toPure_2779_);
lean_closure_set(v___f_2782_, 4, v_tail_2775_);
lean_closure_set(v___f_2782_, 5, v_inst_2769_);
lean_closure_set(v___f_2782_, 6, v_f_2770_);
lean_closure_set(v___f_2782_, 7, v_toBind_2773_);
v___x_2783_ = lean_apply_4(v_toBind_2773_, lean_box(0), lean_box(0), v___x_2780_, v___f_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2784_, lean_object* v_m_2785_, lean_object* v_inst_2786_, lean_object* v_00_u03b2_2787_, lean_object* v_f_2788_, lean_object* v_t_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2786_, v_f_2788_, v_t_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2791_, lean_object* v_x_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_apply_1(v_f_2791_, v_x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2794_, lean_object* v_t_2795_){
_start:
{
lean_object* v___f_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2796_, 0, v_f_2794_);
v___x_2797_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2798_ = l_Lean_PersistentArray_mapM___redArg(v___x_2797_, v___f_2796_, v_t_2795_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2799_, lean_object* v_00_u03b2_2800_, lean_object* v_f_2801_, lean_object* v_t_2802_){
_start:
{
lean_object* v___f_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___f_2803_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2803_, 0, v_f_2801_);
v___x_2804_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2805_ = l_Lean_PersistentArray_mapM___redArg(v___x_2804_, v___f_2803_, v_t_2802_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
if (lean_obj_tag(v_x_2806_) == 0)
{
lean_object* v_cs_2809_; lean_object* v_numNodes_2810_; lean_object* v_depth_2811_; lean_object* v_tailSize_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2834_; 
v_cs_2809_ = lean_ctor_get(v_x_2806_, 0);
v_numNodes_2810_ = lean_ctor_get(v_x_2807_, 0);
v_depth_2811_ = lean_ctor_get(v_x_2807_, 1);
v_tailSize_2812_ = lean_ctor_get(v_x_2807_, 2);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_x_2807_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2814_ = v_x_2807_;
v_isShared_2815_ = v_isSharedCheck_2834_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_tailSize_2812_);
lean_inc(v_depth_2811_);
lean_inc(v_numNodes_2810_);
lean_dec(v_x_2807_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2834_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___y_2819_; uint8_t v___x_2833_; 
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = lean_nat_add(v_numNodes_2810_, v___x_2816_);
lean_dec(v_numNodes_2810_);
v___x_2833_ = lean_nat_dec_le(v_x_2808_, v_depth_2811_);
if (v___x_2833_ == 0)
{
lean_dec(v_depth_2811_);
lean_inc(v_x_2808_);
v___y_2819_ = v_x_2808_;
goto v___jp_2818_;
}
else
{
v___y_2819_ = v_depth_2811_;
goto v___jp_2818_;
}
v___jp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v___y_2819_);
lean_ctor_set(v___x_2814_, 0, v___x_2817_);
v___x_2821_ = v___x_2814_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___y_2819_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_tailSize_2812_);
v___x_2821_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = lean_array_get_size(v_cs_2809_);
v___x_2824_ = lean_nat_dec_lt(v___x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_dec(v_x_2808_);
return v___x_2821_;
}
else
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_nat_dec_le(v___x_2823_, v___x_2823_);
if (v___x_2825_ == 0)
{
if (v___x_2824_ == 0)
{
lean_dec(v_x_2808_);
return v___x_2821_;
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2823_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2808_, v_cs_2809_, v___x_2826_, v___x_2827_, v___x_2821_);
lean_dec(v_x_2808_);
return v___x_2828_;
}
}
else
{
size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = lean_usize_of_nat(v___x_2823_);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2808_, v_cs_2809_, v___x_2829_, v___x_2830_, v___x_2821_);
lean_dec(v_x_2808_);
return v___x_2831_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2835_; lean_object* v_depth_2836_; lean_object* v_tailSize_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2850_; 
v_numNodes_2835_ = lean_ctor_get(v_x_2807_, 0);
v_depth_2836_ = lean_ctor_get(v_x_2807_, 1);
v_tailSize_2837_ = lean_ctor_get(v_x_2807_, 2);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2807_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2839_ = v_x_2807_;
v_isShared_2840_ = v_isSharedCheck_2850_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_tailSize_2837_);
lean_inc(v_depth_2836_);
lean_inc(v_numNodes_2835_);
lean_dec(v_x_2807_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2850_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_nat_add(v_numNodes_2835_, v___x_2841_);
lean_dec(v_numNodes_2835_);
v___x_2843_ = lean_nat_dec_le(v_x_2808_, v_depth_2836_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2845_; 
lean_dec(v_depth_2836_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_x_2808_);
lean_ctor_set(v___x_2839_, 0, v___x_2842_);
v___x_2845_ = v___x_2839_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_x_2808_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_tailSize_2837_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
else
{
lean_object* v___x_2848_; 
lean_dec(v_x_2808_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2842_);
v___x_2848_ = v___x_2839_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_depth_2836_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_tailSize_2837_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2851_, lean_object* v_as_2852_, size_t v_i_2853_, size_t v_stop_2854_, lean_object* v_b_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_eq(v_i_2853_, v_stop_2854_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; size_t v___x_2861_; size_t v___x_2862_; 
v___x_2857_ = lean_array_uget_borrowed(v_as_2852_, v_i_2853_);
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = lean_nat_add(v_x_2851_, v___x_2858_);
v___x_2860_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2857_, v_b_2855_, v___x_2859_);
v___x_2861_ = ((size_t)1ULL);
v___x_2862_ = lean_usize_add(v_i_2853_, v___x_2861_);
v_i_2853_ = v___x_2862_;
v_b_2855_ = v___x_2860_;
goto _start;
}
else
{
return v_b_2855_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2851_ = stack[0].m_obj;
lean_object* v_as_2852_ = stack[1].m_obj;
size_t v_i_2853_ = stack[2].m_num;
size_t v_stop_2854_ = stack[3].m_num;
lean_object* v_b_2855_ = stack[4].m_obj;
lean_object* v_res_2864_;
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2851_, v_as_2852_, v_i_2853_, v_stop_2854_, v_b_2855_);
stack->m_obj
 = v_res_2864_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2865_, lean_object* v_as_2866_, lean_object* v_i_2867_, lean_object* v_stop_2868_, lean_object* v_b_2869_){
_start:
{
size_t v_i_boxed_2870_; size_t v_stop_boxed_2871_; lean_object* v_res_2872_; 
v_i_boxed_2870_ = lean_unbox_usize(v_i_2867_);
lean_dec(v_i_2867_);
v_stop_boxed_2871_ = lean_unbox_usize(v_stop_2868_);
lean_dec(v_stop_2868_);
v_res_2872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2865_, v_as_2866_, v_i_boxed_2870_, v_stop_boxed_2871_, v_b_2869_);
lean_dec_ref(v_as_2866_);
lean_dec(v_x_2865_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2873_, lean_object* v_x_2874_, lean_object* v_x_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2873_, v_x_2874_, v_x_2875_);
lean_dec_ref(v_x_2873_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_, lean_object* v_x_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2878_, v_x_2879_, v_x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2882_, v_x_2883_, v_x_2884_, v_x_2885_);
lean_dec_ref(v_x_2883_);
return v_res_2886_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2887_, lean_object* v_x_2888_, lean_object* v_as_2889_, size_t v_i_2890_, size_t v_stop_2891_, lean_object* v_b_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2888_, v_as_2889_, v_i_2890_, v_stop_2891_, v_b_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2888_ = stack[1].m_obj;
lean_object* v_as_2889_ = stack[2].m_obj;
size_t v_i_2890_ = stack[3].m_num;
size_t v_stop_2891_ = stack[4].m_num;
lean_object* v_b_2892_ = stack[5].m_obj;
lean_object* v_res_2894_;
v_res_2894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_box(0), v_x_2888_, v_as_2889_, v_i_2890_, v_stop_2891_, v_b_2892_);
stack->m_obj
 = v_res_2894_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2895_, lean_object* v_x_2896_, lean_object* v_as_2897_, lean_object* v_i_2898_, lean_object* v_stop_2899_, lean_object* v_b_2900_){
_start:
{
size_t v_i_boxed_2901_; size_t v_stop_boxed_2902_; lean_object* v_res_2903_; 
v_i_boxed_2901_ = lean_unbox_usize(v_i_2898_);
lean_dec(v_i_2898_);
v_stop_boxed_2902_ = lean_unbox_usize(v_stop_2899_);
lean_dec(v_stop_2899_);
v_res_2903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2895_, v_x_2896_, v_as_2897_, v_i_boxed_2901_, v_stop_boxed_2902_, v_b_2900_);
lean_dec_ref(v_as_2897_);
lean_dec(v_x_2896_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2904_){
_start:
{
lean_object* v_root_2905_; lean_object* v_tail_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_root_2905_ = lean_ctor_get(v_r_2904_, 0);
v_tail_2906_ = lean_ctor_get(v_r_2904_, 1);
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = lean_array_get_size(v_tail_2906_);
v___x_2909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2907_);
lean_ctor_set(v___x_2909_, 2, v___x_2908_);
v___x_2910_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2905_, v___x_2909_, v___x_2907_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_PersistentArray_stats___redArg(v_r_2911_);
lean_dec_ref(v_r_2911_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2913_, lean_object* v_r_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_PersistentArray_stats___redArg(v_r_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_r_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_PersistentArray_stats(v_00_u03b1_2916_, v_r_2917_);
lean_dec_ref(v_r_2917_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2923_){
_start:
{
lean_object* v_numNodes_2924_; lean_object* v_depth_2925_; lean_object* v_tailSize_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_numNodes_2924_ = lean_ctor_get(v_s_2923_, 0);
lean_inc(v_numNodes_2924_);
v_depth_2925_ = lean_ctor_get(v_s_2923_, 1);
lean_inc(v_depth_2925_);
v_tailSize_2926_ = lean_ctor_get(v_s_2923_, 2);
lean_inc(v_tailSize_2926_);
lean_dec_ref(v_s_2923_);
v___x_2927_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2928_ = l_Nat_reprFast(v_numNodes_2924_);
v___x_2929_ = lean_string_append(v___x_2927_, v___x_2928_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2931_ = lean_string_append(v___x_2929_, v___x_2930_);
v___x_2932_ = l_Nat_reprFast(v_depth_2925_);
v___x_2933_ = lean_string_append(v___x_2931_, v___x_2932_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2935_ = lean_string_append(v___x_2933_, v___x_2934_);
v___x_2936_ = l_Nat_reprFast(v_tailSize_2926_);
v___x_2937_ = lean_string_append(v___x_2935_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2939_ = lean_string_append(v___x_2937_, v___x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2942_, lean_object* v_j_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_zero_2945_; uint8_t v_isZero_2946_; 
v_zero_2945_ = lean_unsigned_to_nat(0u);
v_isZero_2946_ = lean_nat_dec_eq(v_j_2943_, v_zero_2945_);
if (v_isZero_2946_ == 1)
{
lean_dec(v_j_2943_);
lean_dec(v_v_2942_);
return v_a_2944_;
}
else
{
lean_object* v_one_2947_; lean_object* v_n_2948_; lean_object* v___x_2949_; 
v_one_2947_ = lean_unsigned_to_nat(1u);
v_n_2948_ = lean_nat_sub(v_j_2943_, v_one_2947_);
lean_dec(v_j_2943_);
lean_inc(v_v_2942_);
v___x_2949_ = l_Lean_PersistentArray_push___redArg(v_a_2944_, v_v_2942_);
v_j_2943_ = v_n_2948_;
v_a_2944_ = v___x_2949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2951_, lean_object* v_v_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2954_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2952_, v_n_2951_, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2955_, lean_object* v_n_2956_, lean_object* v_v_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_mkPersistentArray___redArg(v_n_2956_, v_v_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2959_, lean_object* v_v_2960_, lean_object* v_n_2961_, lean_object* v_j_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2960_, v_j_2962_, v_a_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2966_, lean_object* v_v_2967_, lean_object* v_n_2968_, lean_object* v_j_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2966_, v_v_2967_, v_n_2968_, v_j_2969_, v_a_2970_, v_a_2971_);
lean_dec(v_n_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2973_, lean_object* v_v_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_mkPersistentArray___redArg(v_n_2973_, v_v_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2976_, lean_object* v_n_2977_, lean_object* v_v_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_mkPersistentArray___redArg(v_n_2977_, v_v_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
if (lean_obj_tag(v_a_2980_) == 0)
{
return v_a_2981_;
}
else
{
lean_object* v_head_2982_; lean_object* v_tail_2983_; lean_object* v___x_2984_; 
v_head_2982_ = lean_ctor_get(v_a_2980_, 0);
lean_inc(v_head_2982_);
v_tail_2983_ = lean_ctor_get(v_a_2980_, 1);
lean_inc(v_tail_2983_);
lean_dec_ref_known(v_a_2980_, 2);
v___x_2984_ = l_Lean_PersistentArray_push___redArg(v_a_2981_, v_head_2982_);
v_a_2980_ = v_tail_2983_;
v_a_2981_ = v___x_2984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object* v_00_u03b1_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_a_2987_, v_a_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object* v_xs_2990_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2991_ = lean_unsigned_to_nat(32u);
v___x_2992_ = lean_mk_empty_array_with_capacity(v___x_2991_);
lean_dec_ref(v___x_2992_);
v___x_2993_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_2994_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_xs_2990_, v___x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object* v_00_u03b1_2995_, lean_object* v_xs_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_List_toPArray_x27___redArg(v_xs_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object* v_xs_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_2999_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = lean_array_get_size(v_xs_2998_);
v___x_3002_ = lean_nat_dec_lt(v___x_3000_, v___x_3001_);
if (v___x_3002_ == 0)
{
return v___x_2999_;
}
else
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_nat_dec_le(v___x_3001_, v___x_3001_);
if (v___x_3003_ == 0)
{
if (v___x_3002_ == 0)
{
return v___x_2999_;
}
else
{
size_t v___x_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = ((size_t)0ULL);
v___x_3005_ = lean_usize_of_nat(v___x_3001_);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2998_, v___x_3004_, v___x_3005_, v___x_2999_);
return v___x_3006_;
}
}
else
{
size_t v___x_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v___x_3007_ = ((size_t)0ULL);
v___x_3008_ = lean_usize_of_nat(v___x_3001_);
v___x_3009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2998_, v___x_3007_, v___x_3008_, v___x_2999_);
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Array_toPArray_x27___redArg(v_xs_3010_);
lean_dec_ref(v_xs_3010_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object* v_00_u03b1_3012_, lean_object* v_xs_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_Array_toPArray_x27___redArg(v_xs_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_3015_, lean_object* v_xs_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Array_toPArray_x27(v_00_u03b1_3015_, v_xs_3016_);
lean_dec_ref(v_xs_3016_);
return v_res_3017_;
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
