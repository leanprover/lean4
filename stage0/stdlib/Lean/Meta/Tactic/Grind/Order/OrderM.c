// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.OrderM
// Imports: public import Lean.Meta.Tactic.Grind.Order.Types
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_getStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "`grind` internal error, invalid order structure id"};
static const lean_object* l_Lean_Meta_Grind_Order_getStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_getStruct___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getStruct___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getStruct___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_getNodeId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "internal `grind` error, term has not been internalized by order module"};
static const lean_object* l_Lean_Meta_Grind_Order_getNodeId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_getNodeId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getNodeId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getNodeId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_getProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "internal `grind` error, failed to construct proof for"};
static const lean_object* l_Lean_Meta_Grind_Order_getProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_getProof___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getProof___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Order_getProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nand"};
static const lean_object* l_Lean_Meta_Grind_Order_getProof___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_getProof___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_getProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_getProof___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___redArg(lean_object* v_structId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___redArg___boxed(lean_object* v_structId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Order_OrderM_run___redArg(v_structId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run(lean_object* v_00_u03b1_29_, lean_object* v_structId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_structId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_OrderM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_structId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Order_OrderM_run(v_00_u03b1_44_, v_structId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_a_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Order_getStructId___redArg(v_a_62_);
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_65_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_65_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Order_getStructId(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v_env_98_; lean_object* v___x_99_; lean_object* v_mctx_100_; lean_object* v_lctx_101_; lean_object* v_options_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_97_ = lean_st_ref_get(v___y_95_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_env_98_);
lean_dec(v___x_97_);
v___x_99_ = lean_st_ref_get(v___y_93_);
v_mctx_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_mctx_100_);
lean_dec(v___x_99_);
v_lctx_101_ = lean_ctor_get(v___y_92_, 2);
v_options_102_ = lean_ctor_get(v___y_94_, 2);
lean_inc_ref(v_options_102_);
lean_inc_ref(v_lctx_101_);
v___x_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_103_, 0, v_env_98_);
lean_ctor_set(v___x_103_, 1, v_mctx_100_);
lean_ctor_set(v___x_103_, 2, v_lctx_101_);
lean_ctor_set(v___x_103_, 3, v_options_102_);
v___x_104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_msgData_91_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_119_ = lean_ctor_get(v___y_116_, 5);
v___x_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0_spec__0(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_119_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getStruct___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getStruct___closed__0));
v___x_139_ = l_Lean_stringToMessageData(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_141_, v_a_149_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_166_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_166_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_structs_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_structs_157_ = lean_ctor_get(v_a_153_, 0);
lean_inc_ref(v_structs_157_);
lean_dec(v_a_153_);
v___x_158_ = lean_array_get_size(v_structs_157_);
v___x_159_ = lean_nat_dec_lt(v_a_140_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref(v_structs_157_);
lean_del_object(v___x_155_);
v___x_160_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getStruct___closed__1, &l_Lean_Meta_Grind_Order_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_Order_getStruct___closed__1);
v___x_161_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v___x_160_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_array_fget(v_structs_157_, v_a_140_);
lean_dec_ref(v_structs_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_152_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_152_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStruct___boxed(lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_Grind_Order_getStruct(v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec(v_a_176_);
lean_dec(v_a_175_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v_msg_189_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___boxed(lean_object* v_00_u03b1_203_, lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0(v_00_u03b1_203_, v_msg_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec(v___y_206_);
lean_dec(v___y_205_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(lean_object* v_a_218_, lean_object* v_f_219_, lean_object* v_s_220_){
_start:
{
lean_object* v_structs_221_; lean_object* v_typeIdOf_222_; lean_object* v_exprToStructId_223_; lean_object* v_termMap_224_; lean_object* v_termMapInv_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_structs_221_ = lean_ctor_get(v_s_220_, 0);
v_typeIdOf_222_ = lean_ctor_get(v_s_220_, 1);
v_exprToStructId_223_ = lean_ctor_get(v_s_220_, 2);
v_termMap_224_ = lean_ctor_get(v_s_220_, 3);
v_termMapInv_225_ = lean_ctor_get(v_s_220_, 4);
v___x_226_ = lean_array_get_size(v_structs_221_);
v___x_227_ = lean_nat_dec_lt(v_a_218_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_f_219_);
return v_s_220_;
}
else
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_239_; 
lean_inc_ref(v_termMapInv_225_);
lean_inc_ref(v_termMap_224_);
lean_inc_ref(v_exprToStructId_223_);
lean_inc_ref(v_typeIdOf_222_);
lean_inc_ref(v_structs_221_);
v_isSharedCheck_239_ = !lean_is_exclusive(v_s_220_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_240_ = lean_ctor_get(v_s_220_, 4);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_s_220_, 3);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_s_220_, 2);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_s_220_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_s_220_, 0);
lean_dec(v_unused_244_);
v___x_229_ = v_s_220_;
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_s_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_v_231_; lean_object* v___x_232_; lean_object* v_xs_x27_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v_v_231_ = lean_array_fget(v_structs_221_, v_a_218_);
v___x_232_ = lean_box(0);
v_xs_x27_233_ = lean_array_fset(v_structs_221_, v_a_218_, v___x_232_);
v___x_234_ = lean_apply_1(v_f_219_, v_v_231_);
v___x_235_ = lean_array_fset(v_xs_x27_233_, v_a_218_, v___x_234_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_235_);
v___x_237_ = v___x_229_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_typeIdOf_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_exprToStructId_223_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_termMap_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_termMapInv_225_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_245_, lean_object* v_f_246_, lean_object* v_s_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0(v_a_245_, v_f_246_, v_s_247_);
lean_dec(v_a_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object* v_f_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_inc(v_a_250_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_253_, 0, v_a_250_);
lean_closure_set(v___f_253_, 1, v_f_249_);
v___x_254_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_255_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_254_, v___f_253_, v_a_251_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg___boxed(lean_object* v_f_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_256_, v_a_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec(v_a_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct(lean_object* v_f_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v_f_261_, v_a_262_, v_a_263_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modifyStruct___boxed(lean_object* v_f_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_Grind_Order_modifyStruct(v_f_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec(v_a_277_);
lean_dec(v_a_276_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object* v_u_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_Order_getStruct(v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_319_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_319_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_319_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_319_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_nodes_307_; lean_object* v_size_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_nodes_307_ = lean_ctor_get(v_a_303_, 14);
lean_inc_ref(v_nodes_307_);
lean_dec(v_a_303_);
v_size_308_ = lean_ctor_get(v_nodes_307_, 2);
v___x_309_ = l_Lean_instInhabitedExpr;
v___x_310_ = lean_nat_dec_lt(v_u_289_, v_size_308_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec_ref(v_nodes_307_);
v___x_311_ = l_outOfBounds___redArg(v___x_309_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_311_);
v___x_313_ = v___x_305_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = l_Lean_PersistentArray_get_x21___redArg(v___x_309_, v_nodes_307_, v_u_289_);
lean_dec_ref(v_nodes_307_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_315_);
v___x_317_ = v___x_305_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_302_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_302_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getExpr___boxed(lean_object* v_u_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Grind_Order_getExpr(v_u_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_u_328_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(lean_object* v_a_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v_key_345_; lean_object* v_value_346_; lean_object* v_tail_347_; uint8_t v___x_348_; 
v_key_345_ = lean_ctor_get(v_x_343_, 0);
v_value_346_ = lean_ctor_get(v_x_343_, 1);
v_tail_347_ = lean_ctor_get(v_x_343_, 2);
v___x_348_ = lean_nat_dec_eq(v_key_345_, v_a_342_);
if (v___x_348_ == 0)
{
v_x_343_ = v_tail_347_;
goto _start;
}
else
{
lean_object* v___x_350_; 
lean_inc(v_value_346_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_value_346_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg___boxed(lean_object* v_a_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_a_351_, v_x_352_);
lean_dec(v_x_352_);
lean_dec(v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object* v_u_354_, lean_object* v_v_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_Grind_Order_getStruct(v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_385_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_385_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_385_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_385_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___y_374_; lean_object* v_targets_379_; lean_object* v_size_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_targets_379_ = lean_ctor_get(v_a_369_, 19);
lean_inc_ref(v_targets_379_);
lean_dec(v_a_369_);
v_size_380_ = lean_ctor_get(v_targets_379_, 2);
v___x_381_ = lean_box(0);
v___x_382_ = lean_nat_dec_lt(v_u_354_, v_size_380_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v_targets_379_);
v___x_383_ = l_outOfBounds___redArg(v___x_381_);
v___y_374_ = v___x_383_;
goto v___jp_373_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_PersistentArray_get_x21___redArg(v___x_381_, v_targets_379_, v_u_354_);
lean_dec_ref(v_targets_379_);
v___y_374_ = v___x_384_;
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_355_, v___y_374_);
lean_dec(v___y_374_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_375_);
v___x_377_ = v___x_371_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_368_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_368_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___boxed(lean_object* v_u_394_, lean_object* v_v_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_u_394_, v_v_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec(v_a_397_);
lean_dec(v_a_396_);
lean_dec(v_v_395_);
lean_dec(v_u_394_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(lean_object* v_00_u03b2_409_, lean_object* v_a_410_, lean_object* v_x_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_a_410_, v_x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___boxed(lean_object* v_00_u03b2_413_, lean_object* v_a_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0(v_00_u03b2_413_, v_a_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec(v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f(lean_object* v_u_417_, lean_object* v_v_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Grind_Order_getStruct(v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_448_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_448_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_448_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_448_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___y_437_; lean_object* v_proofs_442_; lean_object* v_size_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_proofs_442_ = lean_ctor_get(v_a_432_, 20);
lean_inc_ref(v_proofs_442_);
lean_dec(v_a_432_);
v_size_443_ = lean_ctor_get(v_proofs_442_, 2);
v___x_444_ = lean_box(0);
v___x_445_ = lean_nat_dec_lt(v_u_417_, v_size_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v_proofs_442_);
v___x_446_ = l_outOfBounds___redArg(v___x_444_);
v___y_437_ = v___x_446_;
goto v___jp_436_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentArray_get_x21___redArg(v___x_444_, v_proofs_442_, v_u_417_);
lean_dec_ref(v_proofs_442_);
v___y_437_ = v___x_447_;
goto v___jp_436_;
}
v___jp_436_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_AssocList_find_x3f___at___00Lean_Meta_Grind_Order_getDist_x3f_spec__0___redArg(v_v_418_, v___y_437_);
lean_dec(v___y_437_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_438_);
v___x_440_ = v___x_434_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_431_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_431_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof_x3f___boxed(lean_object* v_u_457_, lean_object* v_v_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_Grind_Order_getProof_x3f(v_u_457_, v_v_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec(v_a_460_);
lean_dec(v_a_459_);
lean_dec(v_v_458_);
lean_dec(v_u_457_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_i_474_, lean_object* v_k_475_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_array_get_size(v_keys_472_);
v___x_477_ = lean_nat_dec_lt(v_i_474_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v_i_474_);
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v_k_x27_479_; size_t v___x_480_; size_t v___x_481_; uint8_t v___x_482_; 
v_k_x27_479_ = lean_array_fget_borrowed(v_keys_472_, v_i_474_);
v___x_480_ = lean_ptr_addr(v_k_475_);
v___x_481_ = lean_ptr_addr(v_k_x27_479_);
v___x_482_ = lean_usize_dec_eq(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_i_474_, v___x_483_);
lean_dec(v_i_474_);
v_i_474_ = v___x_484_;
goto _start;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_array_fget_borrowed(v_vals_473_, v_i_474_);
lean_dec(v_i_474_);
lean_inc(v___x_486_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_488_, lean_object* v_vals_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_488_, v_vals_489_, v_i_490_, v_k_491_);
lean_dec_ref(v_k_491_);
lean_dec_ref(v_vals_489_);
lean_dec_ref(v_keys_488_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(lean_object* v_x_493_, size_t v_x_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_es_496_; lean_object* v___x_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v_j_500_; lean_object* v___x_501_; 
v_es_496_ = lean_ctor_get(v_x_493_, 0);
v___x_497_ = lean_box(2);
v___x_498_ = ((size_t)31ULL);
v___x_499_ = lean_usize_land(v_x_494_, v___x_498_);
v_j_500_ = lean_usize_to_nat(v___x_499_);
v___x_501_ = lean_array_get_borrowed(v___x_497_, v_es_496_, v_j_500_);
lean_dec(v_j_500_);
switch(lean_obj_tag(v___x_501_))
{
case 0:
{
lean_object* v_key_502_; lean_object* v_val_503_; size_t v___x_504_; size_t v___x_505_; uint8_t v___x_506_; 
v_key_502_ = lean_ctor_get(v___x_501_, 0);
v_val_503_ = lean_ctor_get(v___x_501_, 1);
v___x_504_ = lean_ptr_addr(v_x_495_);
v___x_505_ = lean_ptr_addr(v_key_502_);
v___x_506_ = lean_usize_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
else
{
lean_object* v___x_508_; 
lean_inc(v_val_503_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v_val_503_);
return v___x_508_;
}
}
case 1:
{
lean_object* v_node_509_; size_t v___x_510_; size_t v___x_511_; 
v_node_509_ = lean_ctor_get(v___x_501_, 0);
v___x_510_ = ((size_t)5ULL);
v___x_511_ = lean_usize_shift_right(v_x_494_, v___x_510_);
v_x_493_ = v_node_509_;
v_x_494_ = v___x_511_;
goto _start;
}
default: 
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
}
else
{
lean_object* v_ks_514_; lean_object* v_vs_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_ks_514_ = lean_ctor_get(v_x_493_, 0);
v_vs_515_ = lean_ctor_get(v_x_493_, 1);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_ks_514_, v_vs_515_, v___x_516_, v_x_495_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v_x_1319__boxed_521_; lean_object* v_res_522_; 
v_x_1319__boxed_521_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_res_522_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_518_, v_x_1319__boxed_521_, v_x_520_);
lean_dec_ref(v_x_520_);
lean_dec_ref(v_x_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; uint64_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_525_ = lean_ptr_addr(v_x_524_);
v___x_526_ = ((size_t)3ULL);
v___x_527_ = lean_usize_shift_right(v___x_525_, v___x_526_);
v___x_528_ = lean_usize_to_uint64(v___x_527_);
v___x_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_523_, v___x_529_, v_x_524_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg___boxed(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_x_531_, v_x_532_);
lean_dec_ref(v_x_532_);
lean_dec_ref(v_x_531_);
return v_res_533_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getNodeId___closed__0));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object* v_e_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_Grind_Order_getStruct(v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_565_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_565_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_565_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_565_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_nodeMap_555_; lean_object* v___x_556_; 
v_nodeMap_555_ = lean_ctor_get(v_a_551_, 15);
lean_inc_ref(v_nodeMap_555_);
lean_dec(v_a_551_);
v___x_556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_nodeMap_555_, v_e_537_);
lean_dec_ref(v_nodeMap_555_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_559_; 
lean_dec_ref(v_e_537_);
v_val_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v___x_556_, 1);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v_val_557_);
v___x_559_ = v___x_553_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_val_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_556_);
lean_del_object(v___x_553_);
v___x_561_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getNodeId___closed__1, &l_Lean_Meta_Grind_Order_getNodeId___closed__1_once, _init_l_Lean_Meta_Grind_Order_getNodeId___closed__1);
v___x_562_ = l_Lean_indentExpr(v_e_537_);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v___x_563_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_564_;
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v_e_537_);
v_a_566_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_550_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_550_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getNodeId___boxed(lean_object* v_e_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Grind_Order_getNodeId(v_e_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(lean_object* v_00_u03b2_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_x_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___boxed(lean_object* v_00_u03b2_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0(v_00_u03b2_592_, v_x_593_, v_x_594_);
lean_dec_ref(v_x_594_);
lean_dec_ref(v_x_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(lean_object* v_00_u03b2_596_, lean_object* v_x_597_, size_t v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___redArg(v_x_597_, v_x_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
size_t v_x_1454__boxed_605_; lean_object* v_res_606_; 
v_x_1454__boxed_605_ = lean_unbox_usize(v_x_603_);
lean_dec(v_x_603_);
v_res_606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0(v_00_u03b2_601_, v_x_602_, v_x_1454__boxed_605_, v_x_604_);
lean_dec_ref(v_x_604_);
lean_dec_ref(v_x_602_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_607_, lean_object* v_keys_608_, lean_object* v_vals_609_, lean_object* v_heq_610_, lean_object* v_i_611_, lean_object* v_k_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___redArg(v_keys_608_, v_vals_609_, v_i_611_, v_k_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_614_, lean_object* v_keys_615_, lean_object* v_vals_616_, lean_object* v_heq_617_, lean_object* v_i_618_, lean_object* v_k_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0_spec__0_spec__1(v_00_u03b2_614_, v_keys_615_, v_vals_616_, v_heq_617_, v_i_618_, v_k_619_);
lean_dec_ref(v_k_619_);
lean_dec_ref(v_vals_616_);
lean_dec_ref(v_keys_615_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getProof___closed__1(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getProof___closed__0));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_getProof___closed__3(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Meta_Grind_Order_getProof___closed__2));
v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof(lean_object* v_u_627_, lean_object* v_v_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Meta_Grind_Order_getProof_x3f(v_u_627_, v_v_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_678_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_678_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_678_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_678_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
if (lean_obj_tag(v_a_642_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_648_; 
v_val_646_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_a_642_, 1);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_val_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_val_646_);
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
lean_object* v___x_650_; 
lean_del_object(v___x_644_);
lean_dec(v_a_642_);
v___x_650_ = l_Lean_Meta_Grind_Order_getExpr(v_u_627_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = l_Lean_Meta_Grind_Order_getExpr(v_v_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getProof___closed__1, &l_Lean_Meta_Grind_Order_getProof___closed__1_once, _init_l_Lean_Meta_Grind_Order_getProof___closed__1);
v___x_655_ = l_Lean_indentExpr(v_a_651_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_obj_once(&l_Lean_Meta_Grind_Order_getProof___closed__3, &l_Lean_Meta_Grind_Order_getProof___closed__3_once, _init_l_Lean_Meta_Grind_Order_getProof___closed__3);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_indentExpr(v_a_653_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_throwError___at___00Lean_Meta_Grind_Order_getStruct_spec__0___redArg(v___x_660_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
return v___x_661_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_a_651_);
v_a_662_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_652_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_652_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_650_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_650_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_641_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_641_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getProof___boxed(lean_object* v_u_687_, lean_object* v_v_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_Grind_Order_getProof(v_u_687_, v_v_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec(v_a_690_);
lean_dec(v_a_689_);
lean_dec(v_v_688_);
lean_dec(v_u_687_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f(lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Grind_Order_getStruct(v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_cnstrs_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_cnstrs_720_ = lean_ctor_get(v_a_716_, 16);
lean_inc_ref(v_cnstrs_720_);
lean_dec(v_a_716_);
v___x_721_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getNodeId_spec__0___redArg(v_cnstrs_720_, v_e_702_);
lean_dec_ref(v_cnstrs_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_715_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_715_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___boxed(lean_object* v_e_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_e_734_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isRing(lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Grind_Order_getStruct(v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_776_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_776_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_776_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_776_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_ringId_x3f_765_; 
v_ringId_x3f_765_ = lean_ctor_get(v_a_761_, 9);
lean_inc(v_ringId_x3f_765_);
lean_dec(v_a_761_);
if (lean_obj_tag(v_ringId_x3f_765_) == 0)
{
uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_766_ = 0;
v___x_767_ = lean_box(v___x_766_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_767_);
v___x_769_ = v___x_763_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec_ref_known(v_ringId_x3f_765_, 1);
v___x_771_ = 1;
v___x_772_ = lean_box(v___x_771_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_772_);
v___x_774_ = v___x_763_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_777_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_760_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_760_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isRing___boxed(lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Meta_Grind_Order_isRing(v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec(v_a_786_);
lean_dec(v_a_785_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isPartialOrder(lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_Grind_Order_getStruct(v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_826_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_826_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_826_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_826_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_isPartialInst_x3f_815_; 
v_isPartialInst_x3f_815_ = lean_ctor_get(v_a_811_, 6);
lean_inc(v_isPartialInst_x3f_815_);
lean_dec(v_a_811_);
if (lean_obj_tag(v_isPartialInst_x3f_815_) == 0)
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_816_ = 0;
v___x_817_ = lean_box(v___x_816_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec_ref_known(v_isPartialInst_x3f_815_, 1);
v___x_821_ = 1;
v___x_822_ = lean_box(v___x_821_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_822_);
v___x_824_ = v___x_813_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_810_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_810_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isPartialOrder___boxed(lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
lean_dec(v_a_835_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder(lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Grind_Order_getStruct(v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_876_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_876_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_isLinearPreInst_x3f_865_; 
v_isLinearPreInst_x3f_865_ = lean_ctor_get(v_a_861_, 7);
lean_inc(v_isLinearPreInst_x3f_865_);
lean_dec(v_a_861_);
if (lean_obj_tag(v_isLinearPreInst_x3f_865_) == 0)
{
uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = 0;
v___x_867_ = lean_box(v___x_866_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_867_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec_ref_known(v_isLinearPreInst_x3f_865_, 1);
v___x_871_ = 1;
v___x_872_ = lean_box(v___x_871_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_872_);
v___x_874_ = v___x_863_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_860_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_860_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder___boxed(lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec(v_a_886_);
lean_dec(v_a_885_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_hasLt(lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_Grind_Order_getStruct(v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_926_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_926_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_926_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_926_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_lawfulOrderLTInst_x3f_915_; 
v_lawfulOrderLTInst_x3f_915_ = lean_ctor_get(v_a_911_, 8);
lean_inc(v_lawfulOrderLTInst_x3f_915_);
lean_dec(v_a_911_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_915_) == 0)
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = 0;
v___x_917_ = lean_box(v___x_916_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_917_);
v___x_919_ = v___x_913_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
else
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_915_, 1);
v___x_921_ = 1;
v___x_922_ = lean_box(v___x_921_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_922_);
v___x_924_ = v___x_913_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_910_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_910_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_hasLt___boxed(lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_Grind_Order_hasLt(v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec(v_a_936_);
lean_dec(v_a_935_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isInt(lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_Grind_Order_getStruct(v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_953_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_975_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_975_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_975_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_975_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_type_967_; size_t v___x_968_; size_t v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v_type_967_ = lean_ctor_get(v_a_961_, 1);
lean_inc_ref(v_type_967_);
lean_dec(v_a_961_);
v___x_968_ = lean_ptr_addr(v_type_967_);
lean_dec_ref(v_type_967_);
v___x_969_ = lean_ptr_addr(v_a_963_);
lean_dec(v_a_963_);
v___x_970_ = lean_usize_dec_eq(v___x_968_, v___x_969_);
v___x_971_ = lean_box(v___x_970_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_971_);
v___x_973_ = v___x_965_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_961_);
v_a_976_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_962_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_962_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
v_a_984_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_960_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_960_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_isInt___boxed(lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Meta_Grind_Order_isInt(v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec(v_a_993_);
lean_dec(v_a_992_);
return v_res_1004_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
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
