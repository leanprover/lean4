// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Types
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instInhabitedCnstrKind;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedWeight;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedProofInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedToPropagate;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedStruct;
static const lean_array_object l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_orderExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(lean_object* v_le_27_){
_start:
{
lean_inc(v_le_27_);
return v_le_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg___boxed(lean_object* v_le_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(v_le_28_);
lean_dec(v_le_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_le_33_){
_start:
{
lean_inc(v_le_33_);
return v_le_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_le_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_le_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_le_37_);
lean_dec(v_le_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(lean_object* v_lt_40_){
_start:
{
lean_inc(v_lt_40_);
return v_lt_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg___boxed(lean_object* v_lt_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(v_lt_41_);
lean_dec(v_lt_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_lt_46_){
_start:
{
lean_inc(v_lt_46_);
return v_lt_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_lt_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_lt_50_);
lean_dec(v_lt_50_);
return v_res_52_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default(void){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind(void){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2));
v___x_62_ = l_Lean_Expr_const___override(v___x_61_, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(lean_object* v_inst_63_){
_start:
{
uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_64_ = 0;
v___x_65_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0, &l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0);
v___x_66_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3);
v___x_67_ = lean_box(0);
lean_inc(v_inst_63_);
v___x_68_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_68_, 0, v_inst_63_);
lean_ctor_set(v___x_68_, 1, v_inst_63_);
lean_ctor_set(v___x_68_, 2, v___x_65_);
lean_ctor_set(v___x_68_, 3, v___x_66_);
lean_ctor_set(v___x_68_, 4, v___x_67_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*5, v___x_64_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr_default(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr___redArg(lean_object* v_inst_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instInhabitedCnstr(lean_object* v_a_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0(void){
_start:
{
uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = 0;
v___x_78_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0, &l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0);
v___x_79_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*1, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0, &l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once, _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedWeight(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3);
v___x_83_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0, &l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once, _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default;
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(lean_object* v_x_88_){
_start:
{
switch(lean_obj_tag(v_x_88_))
{
case 0:
{
lean_object* v___x_89_; 
v___x_89_ = lean_unsigned_to_nat(0u);
return v___x_89_;
}
case 1:
{
lean_object* v___x_90_; 
v___x_90_ = lean_unsigned_to_nat(1u);
return v___x_90_;
}
default: 
{
lean_object* v___x_91_; 
v___x_91_ = lean_unsigned_to_nat(2u);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx___boxed(lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(v_x_92_);
lean_dec_ref(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(lean_object* v_t_94_, lean_object* v_k_95_){
_start:
{
if (lean_obj_tag(v_t_94_) == 2)
{
lean_object* v_u_96_; lean_object* v_v_97_; lean_object* v___x_98_; 
v_u_96_ = lean_ctor_get(v_t_94_, 0);
lean_inc(v_u_96_);
v_v_97_ = lean_ctor_get(v_t_94_, 1);
lean_inc(v_v_97_);
lean_dec_ref(v_t_94_);
v___x_98_ = lean_apply_2(v_k_95_, v_u_96_, v_v_97_);
return v___x_98_;
}
else
{
lean_object* v_c_99_; lean_object* v_e_100_; lean_object* v_u_101_; lean_object* v_v_102_; lean_object* v_k_103_; lean_object* v_k_x27_104_; lean_object* v___x_105_; 
v_c_99_ = lean_ctor_get(v_t_94_, 0);
lean_inc_ref(v_c_99_);
v_e_100_ = lean_ctor_get(v_t_94_, 1);
lean_inc_ref(v_e_100_);
v_u_101_ = lean_ctor_get(v_t_94_, 2);
lean_inc(v_u_101_);
v_v_102_ = lean_ctor_get(v_t_94_, 3);
lean_inc(v_v_102_);
v_k_103_ = lean_ctor_get(v_t_94_, 4);
lean_inc_ref(v_k_103_);
v_k_x27_104_ = lean_ctor_get(v_t_94_, 5);
lean_inc_ref(v_k_x27_104_);
lean_dec_ref(v_t_94_);
v___x_105_ = lean_apply_6(v_k_95_, v_c_99_, v_e_100_, v_u_101_, v_v_102_, v_k_103_, v_k_x27_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(lean_object* v_motive_106_, lean_object* v_ctorIdx_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_k_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_108_, v_k_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___boxed(lean_object* v_motive_112_, lean_object* v_ctorIdx_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_k_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(v_motive_112_, v_ctorIdx_113_, v_t_114_, v_h_115_, v_k_116_);
lean_dec(v_ctorIdx_113_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim___redArg(lean_object* v_t_118_, lean_object* v_eqTrue_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_118_, v_eqTrue_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_eqTrue_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_122_, v_eqTrue_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim___redArg(lean_object* v_t_126_, lean_object* v_eqFalse_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_126_, v_eqFalse_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim(lean_object* v_motive_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_eqFalse_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_130_, v_eqFalse_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eq_elim___redArg(lean_object* v_t_134_, lean_object* v_eq_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_134_, v_eq_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_eq_elim(lean_object* v_motive_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_eq_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_138_, v_eq_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3);
v___x_147_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0, &l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once, _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0);
v___x_148_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_145_);
lean_ctor_set(v___x_148_, 3, v___x_145_);
lean_ctor_set(v___x_148_, 4, v___x_144_);
lean_ctor_set(v___x_148_, 5, v___x_144_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1, &l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1_once, _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate(void){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default;
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(32u);
v___x_152_ = lean_mk_empty_array_with_capacity(v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_154_ = ((size_t)5ULL);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_unsigned_to_nat(32u);
v___x_157_ = lean_mk_empty_array_with_capacity(v___x_156_);
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0);
v___x_159_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_155_);
lean_ctor_set(v___x_159_, 3, v___x_155_);
lean_ctor_set_usize(v___x_159_, 4, v___x_154_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3);
v___x_165_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1);
v___x_166_ = 0;
v___x_167_ = lean_box(0);
v___x_168_ = lean_box(0);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
lean_ctor_set(v___x_171_, 3, v___x_169_);
lean_ctor_set(v___x_171_, 4, v___x_169_);
lean_ctor_set(v___x_171_, 5, v___x_167_);
lean_ctor_set(v___x_171_, 6, v___x_167_);
lean_ctor_set(v___x_171_, 7, v___x_167_);
lean_ctor_set(v___x_171_, 8, v___x_167_);
lean_ctor_set(v___x_171_, 9, v___x_167_);
lean_ctor_set(v___x_171_, 10, v___x_167_);
lean_ctor_set(v___x_171_, 11, v___x_167_);
lean_ctor_set(v___x_171_, 12, v___x_169_);
lean_ctor_set(v___x_171_, 13, v___x_167_);
lean_ctor_set(v___x_171_, 14, v___x_165_);
lean_ctor_set(v___x_171_, 15, v___x_164_);
lean_ctor_set(v___x_171_, 16, v___x_164_);
lean_ctor_set(v___x_171_, 17, v___x_164_);
lean_ctor_set(v___x_171_, 18, v___x_165_);
lean_ctor_set(v___x_171_, 19, v___x_165_);
lean_ctor_set(v___x_171_, 20, v___x_165_);
lean_ctor_set(v___x_171_, 21, v___x_163_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*22, v___x_166_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedStruct(void){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_Grind_Order_instInhabitedStruct_default;
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2);
v___x_180_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0));
v___x_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_179_);
lean_ctor_set(v___x_181_, 3, v___x_179_);
lean_ctor_set(v___x_181_, 4, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedState_default(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instInhabitedState(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Grind_Order_instInhabitedState_default;
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(lean_object* v___x_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(lean_object* v___x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(v___x_187_);
return v_res_189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_190_; lean_object* v___f_191_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3);
v___f_191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_191_, 0, v___x_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_193_; lean_object* v___x_194_; 
v___f_193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_);
v___x_194_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_201_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_200_, v_a_197_, v_a_198_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg___boxed(lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_202_, v_a_203_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27(lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_206_, v_a_214_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_get_x27___boxed(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Grind_Order_get_x27(v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec(v_a_218_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27___redArg(lean_object* v_f_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_234_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_233_, v_f_230_, v_a_231_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27___redArg___boxed(lean_object* v_f_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_Grind_Order_modify_x27___redArg(v_f_235_, v_a_236_);
lean_dec(v_a_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27(lean_object* v_f_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_252_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_251_, v_f_239_, v_a_240_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_modify_x27___boxed(lean_object* v_f_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Grind_Order_modify_x27(v_f_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec(v_a_254_);
return v_res_265_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default = _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default();
l_Lean_Meta_Grind_Order_instInhabitedCnstrKind = _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind();
l_Lean_Meta_Grind_Order_instInhabitedWeight_default = _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight_default);
l_Lean_Meta_Grind_Order_instInhabitedWeight = _init_l_Lean_Meta_Grind_Order_instInhabitedWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight);
l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default = _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default);
l_Lean_Meta_Grind_Order_instInhabitedProofInfo = _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo);
l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default = _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default);
l_Lean_Meta_Grind_Order_instInhabitedToPropagate = _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate);
l_Lean_Meta_Grind_Order_instInhabitedStruct_default = _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct_default);
l_Lean_Meta_Grind_Order_instInhabitedStruct = _init_l_Lean_Meta_Grind_Order_instInhabitedStruct();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct);
l_Lean_Meta_Grind_Order_instInhabitedState_default = _init_l_Lean_Meta_Grind_Order_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState_default);
l_Lean_Meta_Grind_Order_instInhabitedState = _init_l_Lean_Meta_Grind_Order_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState);
res = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_Order_orderExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_Order_orderExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
}
#ifdef __cplusplus
}
#endif
