// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.OrderM
// Imports: public import Lean.Meta.Tactic.Grind.Order.Types public import Lean.Meta.Sym.Arith.Types
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
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_getOrder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "`grind` internal error, invalid order structure id"};
static const lean_object* l_Lean_Meta_Grind_Order_getOrder___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_getOrder___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getOrder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getOrder___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Order_getStruct___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getStruct___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "internal `grind` error, term has not been internalized by order module"};
static const lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_getProof___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "internal `grind` error, failed to construct proof for"};
static const lean_object* l_Lean_Meta_Grind_Order_getProof___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_getProof___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getProof___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getProof___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Order_getProof___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nand"};
static const lean_object* l_Lean_Meta_Grind_Order_getProof___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_getProof___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getProof___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getProof___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isPartialOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_hasLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_hasLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_OrderM_run___redArg(lean_object* v_structId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_structId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_OrderM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Meta_Grind_Order_OrderM_run___redArg(v_structId_1_, v_x_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___redArg___boxed(lean_object* v_structId_16_, lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Order_OrderM_run___redArg(v_structId_16_, v_x_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec(v_a_18_);
return v_res_29_;
}
}
lean_object* l_Lean_Meta_Grind_Order_OrderM_run(lean_object* v_00_u03b1_30_, lean_object* v_structId_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
lean_inc(v_a_40_);
lean_inc_ref(v_a_39_);
lean_inc(v_a_38_);
lean_inc_ref(v_a_37_);
lean_inc(v_a_36_);
lean_inc_ref(v_a_35_);
lean_inc(v_a_34_);
lean_inc(v_a_33_);
v___x_44_ = lean_apply_12(v_x_32_, v_structId_31_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_OrderM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_31_ = stack[1].m_obj;
lean_object* v_x_32_ = stack[2].m_obj;
lean_object* v_a_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_a_35_ = stack[5].m_obj;
lean_object* v_a_36_ = stack[6].m_obj;
lean_object* v_a_37_ = stack[7].m_obj;
lean_object* v_a_38_ = stack[8].m_obj;
lean_object* v_a_39_ = stack[9].m_obj;
lean_object* v_a_40_ = stack[10].m_obj;
lean_object* v_a_41_ = stack[11].m_obj;
lean_object* v_a_42_ = stack[12].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_Grind_Order_OrderM_run(lean_box(0), v_structId_31_, v_x_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___boxed(lean_object* v_00_u03b1_46_, lean_object* v_structId_47_, lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Grind_Order_OrderM_run(v_00_u03b1_46_, v_structId_47_, v_x_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec(v_a_49_);
return v_res_60_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getStructId___redArg(lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
lean_inc(v_a_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getStructId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_61_ = stack[0].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_Meta_Grind_Order_getStructId___redArg(v_a_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___redArg___boxed(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_Grind_Order_getStructId___redArg(v_a_65_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getStructId(lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
lean_inc(v_a_68_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_a_68_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getStructId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_68_ = stack[0].m_obj;
lean_object* v_a_69_ = stack[1].m_obj;
lean_object* v_a_70_ = stack[2].m_obj;
lean_object* v_a_71_ = stack[3].m_obj;
lean_object* v_a_72_ = stack[4].m_obj;
lean_object* v_a_73_ = stack[5].m_obj;
lean_object* v_a_74_ = stack[6].m_obj;
lean_object* v_a_75_ = stack[7].m_obj;
lean_object* v_a_76_ = stack[8].m_obj;
lean_object* v_a_77_ = stack[9].m_obj;
lean_object* v_a_78_ = stack[10].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Meta_Grind_Order_getStructId(v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___boxed(lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Grind_Order_getStructId(v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec(v_a_83_);
lean_dec(v_a_82_);
return v_res_94_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; lean_object* v_env_102_; uint8_t v___x_103_; lean_object* v_env_104_; lean_object* v___x_105_; lean_object* v_toCold_106_; lean_object* v_mctx_107_; lean_object* v_lctx_108_; lean_object* v_options_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_101_ = lean_st_ref_get(v___y_99_);
v_env_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_env_102_);
lean_dec(v___x_101_);
v___x_103_ = 0;
v_env_104_ = l_Lean_Environment_setRecordingDeps(v_env_102_, v___x_103_);
v___x_105_ = lean_st_ref_get(v___y_97_);
v_toCold_106_ = lean_ctor_get(v___y_98_, 0);
v_mctx_107_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_mctx_107_);
lean_dec(v___x_105_);
v_lctx_108_ = lean_ctor_get(v___y_96_, 2);
v_options_109_ = lean_ctor_get(v_toCold_106_, 2);
lean_inc_ref(v_options_109_);
lean_inc_ref(v_lctx_108_);
v___x_110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_110_, 0, v_env_104_);
lean_ctor_set(v___x_110_, 1, v_mctx_107_);
lean_ctor_set(v___x_110_, 2, v_lctx_108_);
lean_ctor_set(v___x_110_, 3, v_options_109_);
v___x_111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_msgData_95_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_95_ = stack[0].m_obj;
lean_object* v___y_96_ = stack[1].m_obj;
lean_object* v___y_97_ = stack[2].m_obj;
lean_object* v___y_98_ = stack[3].m_obj;
lean_object* v___y_99_ = stack[4].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0(v_msgData_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0___boxed(lean_object* v_msgData_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0(v_msgData_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_120_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_ref_127_; lean_object* v___x_128_; lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_ref_127_ = lean_ctor_get(v___y_124_, 2);
v___x_128_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_spec__0(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_inc(v_ref_127_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_ref_127_);
lean_ctor_set(v___x_133_, 1, v_a_129_);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_121_ = stack[0].m_obj;
lean_object* v___y_122_ = stack[1].m_obj;
lean_object* v___y_123_ = stack[2].m_obj;
lean_object* v___y_124_ = stack[3].m_obj;
lean_object* v___y_125_ = stack[4].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg___boxed(lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getOrder___closed__1(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getOrder___closed__0));
v___x_148_ = l_Lean_stringToMessageData(v___x_147_);
return v___x_148_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getOrder(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_155_, v_a_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_175_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_175_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_orders_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_orders_166_ = lean_ctor_get(v_a_162_, 6);
lean_inc_ref(v_orders_166_);
lean_dec(v_a_162_);
v___x_167_ = lean_array_get_size(v_orders_166_);
v___x_168_ = lean_nat_dec_lt(v_a_149_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec_ref(v_orders_166_);
lean_del_object(v___x_164_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getOrder___closed__1, &l_Lean_Meta_Grind_Order_getOrder___closed__1_once, _init_l_Lean_Meta_Grind_Order_getOrder___closed__1);
v___x_170_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(v___x_169_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_array_fget(v_orders_166_, v_a_149_);
lean_dec_ref(v_orders_166_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_173_ = v___x_164_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_a_176_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_161_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_161_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getOrder_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_149_ = stack[0].m_obj;
lean_object* v_a_150_ = stack[1].m_obj;
lean_object* v_a_151_ = stack[2].m_obj;
lean_object* v_a_152_ = stack[3].m_obj;
lean_object* v_a_153_ = stack[4].m_obj;
lean_object* v_a_154_ = stack[5].m_obj;
lean_object* v_a_155_ = stack[6].m_obj;
lean_object* v_a_156_ = stack[7].m_obj;
lean_object* v_a_157_ = stack[8].m_obj;
lean_object* v_a_158_ = stack[9].m_obj;
lean_object* v_a_159_ = stack[10].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Meta_Grind_Order_getOrder(v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getOrder___boxed(lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_Order_getOrder(v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
lean_dec(v_a_185_);
return v_res_197_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0(lean_object* v_00_u03b1_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(v_msg_199_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_199_ = stack[1].m_obj;
lean_object* v___y_200_ = stack[2].m_obj;
lean_object* v___y_201_ = stack[3].m_obj;
lean_object* v___y_202_ = stack[4].m_obj;
lean_object* v___y_203_ = stack[5].m_obj;
lean_object* v___y_204_ = stack[6].m_obj;
lean_object* v___y_205_ = stack[7].m_obj;
lean_object* v___y_206_ = stack[8].m_obj;
lean_object* v___y_207_ = stack[9].m_obj;
lean_object* v___y_208_ = stack[10].m_obj;
lean_object* v___y_209_ = stack[11].m_obj;
lean_object* v___y_210_ = stack[12].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0(lean_box(0), v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___boxed(lean_object* v_00_u03b1_214_, lean_object* v_msg_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0(v_00_u03b1_214_, v_msg_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec(v___y_217_);
lean_dec(v___y_216_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__0(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(32u);
v___x_230_ = lean_mk_empty_array_with_capacity(v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1(void){
_start:
{
size_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_232_ = ((size_t)5ULL);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_unsigned_to_nat(32u);
v___x_235_ = lean_mk_empty_array_with_capacity(v___x_234_);
v___x_236_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___redArg___closed__0, &l_Lean_Meta_Grind_Order_getStruct___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__0);
v___x_237_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_233_);
lean_ctor_set(v___x_237_, 3, v___x_233_);
lean_ctor_set_usize(v___x_237_, 4, v___x_232_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__2(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___redArg___closed__2, &l_Lean_Meta_Grind_Order_getStruct___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__2);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg(lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_242_, v_a_243_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_264_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_264_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_264_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_264_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_structs_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_structs_250_ = lean_ctor_get(v_a_246_, 0);
lean_inc_ref(v_structs_250_);
lean_dec(v_a_246_);
v___x_251_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1, &l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1);
v___x_252_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3, &l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3);
v___x_253_ = lean_box(0);
lean_inc(v_a_241_);
v___x_254_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_254_, 0, v_a_241_);
lean_ctor_set(v___x_254_, 1, v___x_251_);
lean_ctor_set(v___x_254_, 2, v___x_252_);
lean_ctor_set(v___x_254_, 3, v___x_252_);
lean_ctor_set(v___x_254_, 4, v___x_252_);
lean_ctor_set(v___x_254_, 5, v___x_251_);
lean_ctor_set(v___x_254_, 6, v___x_251_);
lean_ctor_set(v___x_254_, 7, v___x_251_);
lean_ctor_set(v___x_254_, 8, v___x_253_);
v___x_255_ = lean_array_get_size(v_structs_250_);
v___x_256_ = lean_nat_dec_lt(v_a_241_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_structs_250_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_254_);
v___x_258_ = v___x_248_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_254_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_254_, 9);
v___x_260_ = lean_array_fget(v_structs_250_, v_a_241_);
lean_dec_ref(v_structs_250_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_260_);
v___x_262_ = v___x_248_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_265_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_245_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_245_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getStruct___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_241_ = stack[0].m_obj;
lean_object* v_a_242_ = stack[1].m_obj;
lean_object* v_a_243_ = stack[2].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_241_, v_a_242_, v_a_243_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg___boxed(lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_274_, v_a_275_, v_a_276_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec(v_a_274_);
return v_res_278_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_279_, v_a_280_, v_a_288_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_279_ = stack[0].m_obj;
lean_object* v_a_280_ = stack[1].m_obj;
lean_object* v_a_281_ = stack[2].m_obj;
lean_object* v_a_282_ = stack[3].m_obj;
lean_object* v_a_283_ = stack[4].m_obj;
lean_object* v_a_284_ = stack[5].m_obj;
lean_object* v_a_285_ = stack[6].m_obj;
lean_object* v_a_286_ = stack[7].m_obj;
lean_object* v_a_287_ = stack[8].m_obj;
lean_object* v_a_288_ = stack[9].m_obj;
lean_object* v_a_289_ = stack[10].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_Meta_Grind_Order_getStruct(v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___boxed(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Grind_Order_getStruct(v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec(v_a_294_);
lean_dec(v_a_293_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(lean_object* v_a_306_, lean_object* v_f_307_, lean_object* v_s_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_structs_317_; lean_object* v_typeIdOf_318_; lean_object* v_exprToStructId_319_; lean_object* v_termMap_320_; lean_object* v_termMapInv_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_339_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_a_306_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(32u);
v___x_312_ = lean_mk_empty_array_with_capacity(v___x_311_);
lean_dec_ref(v___x_312_);
v___x_313_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1, &l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__1);
v___x_314_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3, &l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_getStruct___redArg___closed__3);
v___x_315_ = lean_box(0);
lean_inc(v_a_306_);
v___x_316_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_316_, 0, v_a_306_);
lean_ctor_set(v___x_316_, 1, v___x_313_);
lean_ctor_set(v___x_316_, 2, v___x_314_);
lean_ctor_set(v___x_316_, 3, v___x_314_);
lean_ctor_set(v___x_316_, 4, v___x_314_);
lean_ctor_set(v___x_316_, 5, v___x_313_);
lean_ctor_set(v___x_316_, 6, v___x_313_);
lean_ctor_set(v___x_316_, 7, v___x_313_);
lean_ctor_set(v___x_316_, 8, v___x_315_);
v_structs_317_ = lean_ctor_get(v_s_308_, 0);
v_typeIdOf_318_ = lean_ctor_get(v_s_308_, 1);
v_exprToStructId_319_ = lean_ctor_get(v_s_308_, 2);
v_termMap_320_ = lean_ctor_get(v_s_308_, 3);
v_termMapInv_321_ = lean_ctor_get(v_s_308_, 4);
v_isSharedCheck_339_ = !lean_is_exclusive(v_s_308_);
if (v_isSharedCheck_339_ == 0)
{
v___x_323_ = v_s_308_;
v_isShared_324_ = v_isSharedCheck_339_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_termMapInv_321_);
lean_inc(v_termMap_320_);
lean_inc(v_exprToStructId_319_);
lean_inc(v_typeIdOf_318_);
lean_inc(v_structs_317_);
lean_dec(v_s_308_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_339_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_325_ = l_Array_rightpad___redArg(v___x_310_, v___x_316_, v_structs_317_);
lean_dec(v___x_310_);
v___x_326_ = lean_array_get_size(v___x_325_);
v___x_327_ = lean_nat_dec_lt(v_a_306_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_329_; 
lean_dec_ref(v_f_307_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_329_ = v___x_323_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_typeIdOf_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_exprToStructId_319_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_termMap_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_termMapInv_321_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
else
{
lean_object* v_v_331_; lean_object* v___x_332_; lean_object* v_xs_x27_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v_v_331_ = lean_array_fget(v___x_325_, v_a_306_);
v___x_332_ = lean_box(0);
v_xs_x27_333_ = lean_array_fset(v___x_325_, v_a_306_, v___x_332_);
v___x_334_ = lean_apply_1(v_f_307_, v_v_331_);
v___x_335_ = lean_array_fset(v_xs_x27_333_, v_a_306_, v___x_334_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_335_);
v___x_337_ = v___x_323_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_typeIdOf_318_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_exprToStructId_319_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_termMap_320_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_termMapInv_321_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_340_, lean_object* v_f_341_, lean_object* v_s_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(v_a_340_, v_f_341_, v_s_342_);
lean_dec(v_a_340_);
return v_res_343_;
}
}
lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object* v_f_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_inc(v_a_345_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_348_, 0, v_a_345_);
lean_closure_set(v___f_348_, 1, v_f_344_);
v___x_349_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_350_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_349_, v___f_348_, v_a_346_);
return v___x_350_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_modifyStruct___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_344_ = stack[0].m_obj;
lean_object* v_a_345_ = stack[1].m_obj;
lean_object* v_a_346_ = stack[2].m_obj;
lean_object* v_res_351_;
v_res_351_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_344_, v_a_345_, v_a_346_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(lean_object* v_f_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec(v_a_353_);
return v_res_356_;
}
}
lean_object* l_Lean_Meta_Grind_Order_modifyStruct(lean_object* v_f_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_357_, v_a_358_, v_a_359_);
return v___x_370_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_modifyStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_357_ = stack[0].m_obj;
lean_object* v_a_358_ = stack[1].m_obj;
lean_object* v_a_359_ = stack[2].m_obj;
lean_object* v_a_360_ = stack[3].m_obj;
lean_object* v_a_361_ = stack[4].m_obj;
lean_object* v_a_362_ = stack[5].m_obj;
lean_object* v_a_363_ = stack[6].m_obj;
lean_object* v_a_364_ = stack[7].m_obj;
lean_object* v_a_365_ = stack[8].m_obj;
lean_object* v_a_366_ = stack[9].m_obj;
lean_object* v_a_367_ = stack[10].m_obj;
lean_object* v_a_368_ = stack[11].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Meta_Grind_Order_modifyStruct(v_f_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___boxed(lean_object* v_f_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_Order_modifyStruct(v_f_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
return v_res_385_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getExpr___redArg(lean_object* v_u_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Lean_instInhabitedExpr;
v___x_392_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_408_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_408_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_408_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_408_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_nodes_397_; lean_object* v_size_398_; uint8_t v___x_399_; 
v_nodes_397_ = lean_ctor_get(v_a_393_, 1);
lean_inc_ref(v_nodes_397_);
lean_dec(v_a_393_);
v_size_398_ = lean_ctor_get(v_nodes_397_, 2);
v___x_399_ = lean_nat_dec_lt(v_u_386_, v_size_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_dec_ref(v_nodes_397_);
v___x_400_ = l_outOfBounds___redArg(v___x_391_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_400_);
v___x_402_ = v___x_395_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_PersistentArray_get_x21___redArg(v___x_391_, v_nodes_397_, v_u_386_);
lean_dec_ref(v_nodes_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_404_);
v___x_406_ = v___x_395_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_a_409_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_392_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_392_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_386_ = stack[0].m_obj;
lean_object* v_a_387_ = stack[1].m_obj;
lean_object* v_a_388_ = stack[2].m_obj;
lean_object* v_a_389_ = stack[3].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_386_, v_a_387_, v_a_388_, v_a_389_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___redArg___boxed(lean_object* v_u_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
lean_dec(v_u_418_);
return v_res_423_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object* v_u_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_424_, v_a_425_, v_a_426_, v_a_434_);
return v___x_437_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_424_ = stack[0].m_obj;
lean_object* v_a_425_ = stack[1].m_obj;
lean_object* v_a_426_ = stack[2].m_obj;
lean_object* v_a_427_ = stack[3].m_obj;
lean_object* v_a_428_ = stack[4].m_obj;
lean_object* v_a_429_ = stack[5].m_obj;
lean_object* v_a_430_ = stack[6].m_obj;
lean_object* v_a_431_ = stack[7].m_obj;
lean_object* v_a_432_ = stack[8].m_obj;
lean_object* v_a_433_ = stack[9].m_obj;
lean_object* v_a_434_ = stack[10].m_obj;
lean_object* v_a_435_ = stack[11].m_obj;
lean_object* v_res_438_;
v_res_438_ = l_Lean_Meta_Grind_Order_getExpr(v_u_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___boxed(lean_object* v_u_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Meta_Grind_Order_getExpr(v_u_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec(v_a_441_);
lean_dec(v_a_440_);
lean_dec(v_u_439_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v_key_456_; lean_object* v_value_457_; lean_object* v_tail_458_; uint8_t v___x_459_; 
v_key_456_ = lean_ctor_get(v_x_454_, 0);
v_value_457_ = lean_ctor_get(v_x_454_, 1);
v_tail_458_ = lean_ctor_get(v_x_454_, 2);
v___x_459_ = lean_nat_dec_eq(v_key_456_, v_a_453_);
if (v___x_459_ == 0)
{
v_x_454_ = v_tail_458_;
goto _start;
}
else
{
lean_object* v___x_461_; 
lean_inc(v_value_457_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_value_457_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_a_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_a_462_);
return v_res_464_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___redArg(lean_object* v_u_465_, lean_object* v_v_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_box(0);
v___x_472_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_467_, v_a_468_, v_a_469_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_488_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_488_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_488_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_488_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___y_478_; lean_object* v_targets_483_; lean_object* v_size_484_; uint8_t v___x_485_; 
v_targets_483_ = lean_ctor_get(v_a_473_, 6);
lean_inc_ref(v_targets_483_);
lean_dec(v_a_473_);
v_size_484_ = lean_ctor_get(v_targets_483_, 2);
v___x_485_ = lean_nat_dec_lt(v_u_465_, v_size_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_targets_483_);
v___x_486_ = l_outOfBounds___redArg(v___x_471_);
v___y_478_ = v___x_486_;
goto v___jp_477_;
}
else
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentArray_get_x21___redArg(v___x_471_, v_targets_483_, v_u_465_);
lean_dec_ref(v_targets_483_);
v___y_478_ = v___x_487_;
goto v___jp_477_;
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_466_, v___y_478_);
lean_dec(v___y_478_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_479_);
v___x_481_ = v___x_475_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_472_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_472_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getDist_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_465_ = stack[0].m_obj;
lean_object* v_v_466_ = stack[1].m_obj;
lean_object* v_a_467_ = stack[2].m_obj;
lean_object* v_a_468_ = stack[3].m_obj;
lean_object* v_a_469_ = stack[4].m_obj;
lean_object* v_res_497_;
v_res_497_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_u_465_, v_v_466_, v_a_467_, v_a_468_, v_a_469_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___redArg___boxed(lean_object* v_u_498_, lean_object* v_v_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_u_498_, v_v_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec(v_a_500_);
lean_dec(v_v_499_);
lean_dec(v_u_498_);
return v_res_504_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object* v_u_505_, lean_object* v_v_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_u_505_, v_v_506_, v_a_507_, v_a_508_, v_a_516_);
return v___x_519_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getDist_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_505_ = stack[0].m_obj;
lean_object* v_v_506_ = stack[1].m_obj;
lean_object* v_a_507_ = stack[2].m_obj;
lean_object* v_a_508_ = stack[3].m_obj;
lean_object* v_a_509_ = stack[4].m_obj;
lean_object* v_a_510_ = stack[5].m_obj;
lean_object* v_a_511_ = stack[6].m_obj;
lean_object* v_a_512_ = stack[7].m_obj;
lean_object* v_a_513_ = stack[8].m_obj;
lean_object* v_a_514_ = stack[9].m_obj;
lean_object* v_a_515_ = stack[10].m_obj;
lean_object* v_a_516_ = stack[11].m_obj;
lean_object* v_a_517_ = stack[12].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_u_505_, v_v_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___boxed(lean_object* v_u_521_, lean_object* v_v_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_u_521_, v_v_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec(v_a_524_);
lean_dec(v_a_523_);
lean_dec(v_v_522_);
lean_dec(v_u_521_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(lean_object* v_00_u03b2_536_, lean_object* v_a_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_a_537_, v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(lean_object* v_00_u03b2_540_, lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(v_00_u03b2_540_, v_a_541_, v_x_542_);
lean_dec(v_x_542_);
lean_dec(v_a_541_);
return v_res_543_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___redArg(lean_object* v_u_544_, lean_object* v_v_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(0);
v___x_551_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_546_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_567_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_567_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_567_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___y_557_; lean_object* v_proofs_562_; lean_object* v_size_563_; uint8_t v___x_564_; 
v_proofs_562_ = lean_ctor_get(v_a_552_, 7);
lean_inc_ref(v_proofs_562_);
lean_dec(v_a_552_);
v_size_563_ = lean_ctor_get(v_proofs_562_, 2);
v___x_564_ = lean_nat_dec_lt(v_u_544_, v_size_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
lean_dec_ref(v_proofs_562_);
v___x_565_ = l_outOfBounds___redArg(v___x_550_);
v___y_557_ = v___x_565_;
goto v___jp_556_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_PersistentArray_get_x21___redArg(v___x_550_, v_proofs_562_, v_u_544_);
lean_dec_ref(v_proofs_562_);
v___y_557_ = v___x_566_;
goto v___jp_556_;
}
v___jp_556_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_545_, v___y_557_);
lean_dec(v___y_557_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_558_);
v___x_560_ = v___x_554_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_551_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_551_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getProof_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_544_ = stack[0].m_obj;
lean_object* v_v_545_ = stack[1].m_obj;
lean_object* v_a_546_ = stack[2].m_obj;
lean_object* v_a_547_ = stack[3].m_obj;
lean_object* v_a_548_ = stack[4].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_Meta_Grind_Order_getProof_x3f___redArg(v_u_544_, v_v_545_, v_a_546_, v_a_547_, v_a_548_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___redArg___boxed(lean_object* v_u_577_, lean_object* v_v_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Grind_Order_getProof_x3f___redArg(v_u_577_, v_v_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec(v_a_579_);
lean_dec(v_v_578_);
lean_dec(v_u_577_);
return v_res_583_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getProof_x3f(lean_object* v_u_584_, lean_object* v_v_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_Grind_Order_getProof_x3f___redArg(v_u_584_, v_v_585_, v_a_586_, v_a_587_, v_a_595_);
return v___x_598_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getProof_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_584_ = stack[0].m_obj;
lean_object* v_v_585_ = stack[1].m_obj;
lean_object* v_a_586_ = stack[2].m_obj;
lean_object* v_a_587_ = stack[3].m_obj;
lean_object* v_a_588_ = stack[4].m_obj;
lean_object* v_a_589_ = stack[5].m_obj;
lean_object* v_a_590_ = stack[6].m_obj;
lean_object* v_a_591_ = stack[7].m_obj;
lean_object* v_a_592_ = stack[8].m_obj;
lean_object* v_a_593_ = stack[9].m_obj;
lean_object* v_a_594_ = stack[10].m_obj;
lean_object* v_a_595_ = stack[11].m_obj;
lean_object* v_a_596_ = stack[12].m_obj;
lean_object* v_res_599_;
v_res_599_ = l_Lean_Meta_Grind_Order_getProof_x3f(v_u_584_, v_v_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
stack->m_obj
 = v_res_599_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___boxed(lean_object* v_u_600_, lean_object* v_v_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Meta_Grind_Order_getProof_x3f(v_u_600_, v_v_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec(v_a_603_);
lean_dec(v_a_602_);
lean_dec(v_v_601_);
lean_dec(v_u_600_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_615_, lean_object* v_vals_616_, lean_object* v_i_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_keys_615_);
v___x_620_ = lean_nat_dec_lt(v_i_617_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_i_617_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
lean_object* v_k_x27_622_; size_t v___x_623_; size_t v___x_624_; uint8_t v___x_625_; 
v_k_x27_622_ = lean_array_fget_borrowed(v_keys_615_, v_i_617_);
v___x_623_ = lean_ptr_addr(v_k_618_);
v___x_624_ = lean_ptr_addr(v_k_x27_622_);
v___x_625_ = lean_usize_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_i_617_, v___x_626_);
lean_dec(v_i_617_);
v_i_617_ = v___x_627_;
goto _start;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_array_fget_borrowed(v_vals_616_, v_i_617_);
lean_dec(v_i_617_);
lean_inc(v___x_629_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_631_, lean_object* v_vals_632_, lean_object* v_i_633_, lean_object* v_k_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_631_, v_vals_632_, v_i_633_, v_k_634_);
lean_dec_ref(v_k_634_);
lean_dec_ref(v_vals_632_);
lean_dec_ref(v_keys_631_);
return v_res_635_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(lean_object* v_x_636_, size_t v_x_637_, lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v_es_639_; lean_object* v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v_j_643_; lean_object* v___x_644_; 
v_es_639_ = lean_ctor_get(v_x_636_, 0);
v___x_640_ = lean_box(2);
v___x_641_ = ((size_t)31ULL);
v___x_642_ = lean_usize_land(v_x_637_, v___x_641_);
v_j_643_ = lean_usize_to_nat(v___x_642_);
v___x_644_ = lean_array_get_borrowed(v___x_640_, v_es_639_, v_j_643_);
lean_dec(v_j_643_);
switch(lean_obj_tag(v___x_644_))
{
case 0:
{
lean_object* v_key_645_; lean_object* v_val_646_; size_t v___x_647_; size_t v___x_648_; uint8_t v___x_649_; 
v_key_645_ = lean_ctor_get(v___x_644_, 0);
v_val_646_ = lean_ctor_get(v___x_644_, 1);
v___x_647_ = lean_ptr_addr(v_x_638_);
v___x_648_ = lean_ptr_addr(v_key_645_);
v___x_649_ = lean_usize_dec_eq(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
else
{
lean_object* v___x_651_; 
lean_inc(v_val_646_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v_val_646_);
return v___x_651_;
}
}
case 1:
{
lean_object* v_node_652_; size_t v___x_653_; size_t v___x_654_; 
v_node_652_ = lean_ctor_get(v___x_644_, 0);
v___x_653_ = ((size_t)5ULL);
v___x_654_ = lean_usize_shift_right(v_x_637_, v___x_653_);
v_x_636_ = v_node_652_;
v_x_637_ = v___x_654_;
goto _start;
}
default: 
{
lean_object* v___x_656_; 
v___x_656_ = lean_box(0);
return v___x_656_;
}
}
}
else
{
lean_object* v_ks_657_; lean_object* v_vs_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_ks_657_ = lean_ctor_get(v_x_636_, 0);
v_vs_658_ = lean_ctor_get(v_x_636_, 1);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_ks_657_, v_vs_658_, v___x_659_, v_x_638_);
return v___x_660_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_636_ = stack[0].m_obj;
size_t v_x_637_ = stack[1].m_num;
lean_object* v_x_638_ = stack[2].m_obj;
lean_object* v_res_661_;
v_res_661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_636_, v_x_637_, v_x_638_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
size_t v_x_1293__boxed_665_; lean_object* v_res_666_; 
v_x_1293__boxed_665_ = lean_unbox_usize(v_x_663_);
lean_dec(v_x_663_);
v_res_666_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_662_, v_x_1293__boxed_665_, v_x_664_);
lean_dec_ref(v_x_664_);
lean_dec_ref(v_x_662_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; uint64_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_669_ = lean_ptr_addr(v_x_668_);
v___x_670_ = ((size_t)3ULL);
v___x_671_ = lean_usize_shift_right(v___x_669_, v___x_670_);
v___x_672_ = lean_usize_to_uint64(v___x_671_);
v___x_673_ = lean_uint64_to_usize(v___x_672_);
v___x_674_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_667_, v___x_673_, v_x_668_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_x_675_, v_x_676_);
lean_dec_ref(v_x_676_);
lean_dec_ref(v_x_675_);
return v_res_677_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__0));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg(lean_object* v_e_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_682_, v_a_683_, v_a_686_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_704_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_704_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_704_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_704_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_nodeMap_694_; lean_object* v___x_695_; 
v_nodeMap_694_ = lean_ctor_get(v_a_690_, 2);
lean_inc_ref(v_nodeMap_694_);
lean_dec(v_a_690_);
v___x_695_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_nodeMap_694_, v_e_681_);
lean_dec_ref(v_nodeMap_694_);
if (lean_obj_tag(v___x_695_) == 1)
{
lean_object* v_val_696_; lean_object* v___x_698_; 
lean_dec_ref(v_e_681_);
v_val_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v___x_695_, 1);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_val_696_);
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_val_696_);
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
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v___x_695_);
lean_del_object(v___x_692_);
v___x_700_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__1, &l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_getNodeId___redArg___closed__1);
v___x_701_ = l_Lean_indentExpr(v_e_681_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(v___x_702_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
return v___x_703_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v_e_681_);
v_a_705_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_689_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_689_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getNodeId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_681_ = stack[0].m_obj;
lean_object* v_a_682_ = stack[1].m_obj;
lean_object* v_a_683_ = stack[2].m_obj;
lean_object* v_a_684_ = stack[3].m_obj;
lean_object* v_a_685_ = stack[4].m_obj;
lean_object* v_a_686_ = stack[5].m_obj;
lean_object* v_a_687_ = stack[6].m_obj;
lean_object* v_res_713_;
v_res_713_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_e_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg___boxed(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_e_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec(v_a_715_);
return v_res_722_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object* v_e_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_e_723_, v_a_724_, v_a_725_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_736_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getNodeId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_723_ = stack[0].m_obj;
lean_object* v_a_724_ = stack[1].m_obj;
lean_object* v_a_725_ = stack[2].m_obj;
lean_object* v_a_726_ = stack[3].m_obj;
lean_object* v_a_727_ = stack[4].m_obj;
lean_object* v_a_728_ = stack[5].m_obj;
lean_object* v_a_729_ = stack[6].m_obj;
lean_object* v_a_730_ = stack[7].m_obj;
lean_object* v_a_731_ = stack[8].m_obj;
lean_object* v_a_732_ = stack[9].m_obj;
lean_object* v_a_733_ = stack[10].m_obj;
lean_object* v_a_734_ = stack[11].m_obj;
lean_object* v_res_737_;
v_res_737_ = l_Lean_Meta_Grind_Order_getNodeId(v_e_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
stack->m_obj
 = v_res_737_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___boxed(lean_object* v_e_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_Grind_Order_getNodeId(v_e_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec(v_a_740_);
lean_dec(v_a_739_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(v_00_u03b2_756_, v_x_757_, v_x_758_);
lean_dec_ref(v_x_758_);
lean_dec_ref(v_x_757_);
return v_res_759_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, size_t v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_761_, v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_761_ = stack[1].m_obj;
size_t v_x_762_ = stack[2].m_num;
lean_object* v_x_763_ = stack[3].m_obj;
lean_object* v_res_765_;
v_res_765_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(lean_box(0), v_x_761_, v_x_762_, v_x_763_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
size_t v_x_1506__boxed_770_; lean_object* v_res_771_; 
v_x_1506__boxed_770_ = lean_unbox_usize(v_x_768_);
lean_dec(v_x_768_);
v_res_771_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(v_00_u03b2_766_, v_x_767_, v_x_1506__boxed_770_, v_x_769_);
lean_dec_ref(v_x_769_);
lean_dec_ref(v_x_767_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_772_, lean_object* v_keys_773_, lean_object* v_vals_774_, lean_object* v_heq_775_, lean_object* v_i_776_, lean_object* v_k_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_773_, v_vals_774_, v_i_776_, v_k_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_779_, lean_object* v_keys_780_, lean_object* v_vals_781_, lean_object* v_heq_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(v_00_u03b2_779_, v_keys_780_, v_vals_781_, v_heq_782_, v_i_783_, v_k_784_);
lean_dec_ref(v_k_784_);
lean_dec_ref(v_vals_781_);
lean_dec_ref(v_keys_780_);
return v_res_785_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getProof___redArg___closed__1(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getProof___redArg___closed__0));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getProof___redArg___closed__3(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getProof___redArg___closed__2));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getProof___redArg(lean_object* v_u_792_, lean_object* v_v_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Meta_Grind_Order_getProof_x3f___redArg(v_u_792_, v_v_793_, v_a_794_, v_a_795_, v_a_798_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_838_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_838_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_838_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_838_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
if (lean_obj_tag(v_a_802_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_808_; 
v_val_806_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_a_802_, 1);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_val_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_810_; 
lean_del_object(v___x_804_);
lean_dec(v_a_802_);
v___x_810_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_792_, v_a_794_, v_a_795_, v_a_798_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_793_, v_a_794_, v_a_795_, v_a_798_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getProof___redArg___closed__1, &l_Lean_Meta_Grind_Order_getProof___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_getProof___redArg___closed__1);
v___x_815_ = l_Lean_indentExpr(v_a_811_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getProof___redArg___closed__3, &l_Lean_Meta_Grind_Order_getProof___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_getProof___redArg___closed__3);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_indentExpr(v_a_813_);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getOrder_spec__0___redArg(v___x_820_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_811_);
v_a_822_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_812_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_812_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_810_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_810_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_801_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_801_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getProof___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_792_ = stack[0].m_obj;
lean_object* v_v_793_ = stack[1].m_obj;
lean_object* v_a_794_ = stack[2].m_obj;
lean_object* v_a_795_ = stack[3].m_obj;
lean_object* v_a_796_ = stack[4].m_obj;
lean_object* v_a_797_ = stack[5].m_obj;
lean_object* v_a_798_ = stack[6].m_obj;
lean_object* v_a_799_ = stack[7].m_obj;
lean_object* v_res_847_;
v_res_847_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_u_792_, v_v_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___redArg___boxed(lean_object* v_u_848_, lean_object* v_v_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_u_848_, v_v_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_v_849_);
lean_dec(v_u_848_);
return v_res_857_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getProof(lean_object* v_u_858_, lean_object* v_v_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_u_858_, v_v_859_, v_a_860_, v_a_861_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v___x_872_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_858_ = stack[0].m_obj;
lean_object* v_v_859_ = stack[1].m_obj;
lean_object* v_a_860_ = stack[2].m_obj;
lean_object* v_a_861_ = stack[3].m_obj;
lean_object* v_a_862_ = stack[4].m_obj;
lean_object* v_a_863_ = stack[5].m_obj;
lean_object* v_a_864_ = stack[6].m_obj;
lean_object* v_a_865_ = stack[7].m_obj;
lean_object* v_a_866_ = stack[8].m_obj;
lean_object* v_a_867_ = stack[9].m_obj;
lean_object* v_a_868_ = stack[10].m_obj;
lean_object* v_a_869_ = stack[11].m_obj;
lean_object* v_a_870_ = stack[12].m_obj;
lean_object* v_res_873_;
v_res_873_ = l_Lean_Meta_Grind_Order_getProof(v_u_858_, v_v_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___boxed(lean_object* v_u_874_, lean_object* v_v_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Meta_Grind_Order_getProof(v_u_874_, v_v_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_v_875_);
lean_dec(v_u_874_);
return v_res_888_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(lean_object* v_e_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_904_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_904_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_cnstrs_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v_cnstrs_899_ = lean_ctor_get(v_a_895_, 3);
lean_inc_ref(v_cnstrs_899_);
lean_dec(v_a_895_);
v___x_900_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_cnstrs_899_, v_e_889_);
lean_dec_ref(v_cnstrs_899_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_894_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_894_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_889_ = stack[0].m_obj;
lean_object* v_a_890_ = stack[1].m_obj;
lean_object* v_a_891_ = stack[2].m_obj;
lean_object* v_a_892_ = stack[3].m_obj;
lean_object* v_res_913_;
v_res_913_ = l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(v_e_889_, v_a_890_, v_a_891_, v_a_892_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg___boxed(lean_object* v_e_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(v_e_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_e_914_);
return v_res_919_;
}
}
lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f(lean_object* v_e_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(v_e_920_, v_a_921_, v_a_922_, v_a_930_);
return v___x_933_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_getCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_920_ = stack[0].m_obj;
lean_object* v_a_921_ = stack[1].m_obj;
lean_object* v_a_922_ = stack[2].m_obj;
lean_object* v_a_923_ = stack[3].m_obj;
lean_object* v_a_924_ = stack[4].m_obj;
lean_object* v_a_925_ = stack[5].m_obj;
lean_object* v_a_926_ = stack[6].m_obj;
lean_object* v_a_927_ = stack[7].m_obj;
lean_object* v_a_928_ = stack[8].m_obj;
lean_object* v_a_929_ = stack[9].m_obj;
lean_object* v_a_930_ = stack[10].m_obj;
lean_object* v_a_931_ = stack[11].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___boxed(lean_object* v_e_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_e_935_);
return v_res_948_;
}
}
lean_object* l_Lean_Meta_Grind_Order_isRing(lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Grind_Order_getOrder(v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_977_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_977_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_977_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_977_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_ringId_x3f_966_; 
v_ringId_x3f_966_ = lean_ctor_get(v_a_962_, 9);
lean_inc(v_ringId_x3f_966_);
lean_dec(v_a_962_);
if (lean_obj_tag(v_ringId_x3f_966_) == 0)
{
uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = 0;
v___x_968_ = lean_box(v___x_967_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_968_);
v___x_970_ = v___x_964_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec_ref_known(v_ringId_x3f_966_, 1);
v___x_972_ = 1;
v___x_973_ = lean_box(v___x_972_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_973_);
v___x_975_ = v___x_964_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_961_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_961_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_isRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_949_ = stack[0].m_obj;
lean_object* v_a_950_ = stack[1].m_obj;
lean_object* v_a_951_ = stack[2].m_obj;
lean_object* v_a_952_ = stack[3].m_obj;
lean_object* v_a_953_ = stack[4].m_obj;
lean_object* v_a_954_ = stack[5].m_obj;
lean_object* v_a_955_ = stack[6].m_obj;
lean_object* v_a_956_ = stack[7].m_obj;
lean_object* v_a_957_ = stack[8].m_obj;
lean_object* v_a_958_ = stack[9].m_obj;
lean_object* v_a_959_ = stack[10].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_Lean_Meta_Grind_Order_isRing(v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isRing___boxed(lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_Grind_Order_isRing(v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec(v_a_988_);
lean_dec(v_a_987_);
return v_res_999_;
}
}
lean_object* l_Lean_Meta_Grind_Order_isPartialOrder(lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_Grind_Order_getOrder(v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1028_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1028_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1028_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_isPartialInst_x3f_1017_; 
v_isPartialInst_x3f_1017_ = lean_ctor_get(v_a_1013_, 6);
lean_inc(v_isPartialInst_x3f_1017_);
lean_dec(v_a_1013_);
if (lean_obj_tag(v_isPartialInst_x3f_1017_) == 0)
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = 0;
v___x_1019_ = lean_box(v___x_1018_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1019_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_dec_ref_known(v_isPartialInst_x3f_1017_, 1);
v___x_1023_ = 1;
v___x_1024_ = lean_box(v___x_1023_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1024_);
v___x_1026_ = v___x_1015_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1012_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1012_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_isPartialOrder_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1000_ = stack[0].m_obj;
lean_object* v_a_1001_ = stack[1].m_obj;
lean_object* v_a_1002_ = stack[2].m_obj;
lean_object* v_a_1003_ = stack[3].m_obj;
lean_object* v_a_1004_ = stack[4].m_obj;
lean_object* v_a_1005_ = stack[5].m_obj;
lean_object* v_a_1006_ = stack[6].m_obj;
lean_object* v_a_1007_ = stack[7].m_obj;
lean_object* v_a_1008_ = stack[8].m_obj;
lean_object* v_a_1009_ = stack[9].m_obj;
lean_object* v_a_1010_ = stack[10].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isPartialOrder___boxed(lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec(v_a_1038_);
return v_res_1050_;
}
}
lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Grind_Order_getOrder(v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1079_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1079_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1079_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_isLinearPreInst_x3f_1068_; 
v_isLinearPreInst_x3f_1068_ = lean_ctor_get(v_a_1064_, 7);
lean_inc(v_isLinearPreInst_x3f_1068_);
lean_dec(v_a_1064_);
if (lean_obj_tag(v_isLinearPreInst_x3f_1068_) == 0)
{
uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1069_ = 0;
v___x_1070_ = lean_box(v___x_1069_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
lean_dec_ref_known(v_isLinearPreInst_x3f_1068_, 1);
v___x_1074_ = 1;
v___x_1075_ = lean_box(v___x_1074_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1075_);
v___x_1077_ = v___x_1066_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1063_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1063_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_isLinearPreorder_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1051_ = stack[0].m_obj;
lean_object* v_a_1052_ = stack[1].m_obj;
lean_object* v_a_1053_ = stack[2].m_obj;
lean_object* v_a_1054_ = stack[3].m_obj;
lean_object* v_a_1055_ = stack[4].m_obj;
lean_object* v_a_1056_ = stack[5].m_obj;
lean_object* v_a_1057_ = stack[6].m_obj;
lean_object* v_a_1058_ = stack[7].m_obj;
lean_object* v_a_1059_ = stack[8].m_obj;
lean_object* v_a_1060_ = stack[9].m_obj;
lean_object* v_a_1061_ = stack[10].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder___boxed(lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec(v_a_1089_);
return v_res_1101_;
}
}
lean_object* l_Lean_Meta_Grind_Order_hasLt(lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Meta_Grind_Order_getOrder(v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1130_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1130_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1130_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_lawfulOrderLTInst_x3f_1119_; 
v_lawfulOrderLTInst_x3f_1119_ = lean_ctor_get(v_a_1115_, 8);
lean_inc(v_lawfulOrderLTInst_x3f_1119_);
lean_dec(v_a_1115_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1119_) == 0)
{
uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = 0;
v___x_1121_ = lean_box(v___x_1120_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1121_);
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
else
{
uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1119_, 1);
v___x_1125_ = 1;
v___x_1126_ = lean_box(v___x_1125_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1126_);
v___x_1128_ = v___x_1117_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1114_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1114_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_hasLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1102_ = stack[0].m_obj;
lean_object* v_a_1103_ = stack[1].m_obj;
lean_object* v_a_1104_ = stack[2].m_obj;
lean_object* v_a_1105_ = stack[3].m_obj;
lean_object* v_a_1106_ = stack[4].m_obj;
lean_object* v_a_1107_ = stack[5].m_obj;
lean_object* v_a_1108_ = stack[6].m_obj;
lean_object* v_a_1109_ = stack[7].m_obj;
lean_object* v_a_1110_ = stack[8].m_obj;
lean_object* v_a_1111_ = stack[9].m_obj;
lean_object* v_a_1112_ = stack[10].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_Meta_Grind_Order_hasLt(v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_hasLt___boxed(lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_Grind_Order_hasLt(v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec(v_a_1140_);
return v_res_1152_;
}
}
lean_object* l_Lean_Meta_Grind_Order_isInt(lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_Grind_Order_getOrder(v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_1158_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1180_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_type_1172_; size_t v___x_1173_; size_t v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v_type_1172_ = lean_ctor_get(v_a_1166_, 1);
lean_inc_ref(v_type_1172_);
lean_dec(v_a_1166_);
v___x_1173_ = lean_ptr_addr(v_type_1172_);
lean_dec_ref(v_type_1172_);
v___x_1174_ = lean_ptr_addr(v_a_1168_);
lean_dec(v_a_1168_);
v___x_1175_ = lean_usize_dec_eq(v___x_1173_, v___x_1174_);
v___x_1176_ = lean_box(v___x_1175_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1176_);
v___x_1178_ = v___x_1170_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_1166_);
v_a_1181_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1167_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1167_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_a_1189_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1165_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1165_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_isInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1153_ = stack[0].m_obj;
lean_object* v_a_1154_ = stack[1].m_obj;
lean_object* v_a_1155_ = stack[2].m_obj;
lean_object* v_a_1156_ = stack[3].m_obj;
lean_object* v_a_1157_ = stack[4].m_obj;
lean_object* v_a_1158_ = stack[5].m_obj;
lean_object* v_a_1159_ = stack[6].m_obj;
lean_object* v_a_1160_ = stack[7].m_obj;
lean_object* v_a_1161_ = stack[8].m_obj;
lean_object* v_a_1162_ = stack[9].m_obj;
lean_object* v_a_1163_ = stack[10].m_obj;
lean_object* v_res_1197_;
v_res_1197_ = l_Lean_Meta_Grind_Order_isInt(v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
stack->m_obj
 = v_res_1197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isInt___boxed(lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_Grind_Order_isInt(v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec(v_a_1198_);
return v_res_1210_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
}
#ifdef __cplusplus
}
#endif
