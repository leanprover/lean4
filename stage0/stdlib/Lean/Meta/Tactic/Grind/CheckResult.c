// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CheckResult
// Imports: public import Init.Data.Repr meta import Init.MetaTypes
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCheckResult_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqCheckResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqCheckResult___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqCheckResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqCheckResult = (const lean_object*)&l_Lean_Meta_Grind_instBEqCheckResult___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instInhabitedCheckResult_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instInhabitedCheckResult;
static const lean_string_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Grind.CheckResult.none"};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Grind.CheckResult.progress"};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Grind.CheckResult.propagated"};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Grind.CheckResult.closed"};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprCheckResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprCheckResult_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprCheckResult___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprCheckResult = (const lean_object*)&l_Lean_Meta_Grind_instReprCheckResult___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_le(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_le___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_join(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Lean_Meta_Grind_CheckResult_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Lean_Meta_Grind_CheckResult_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg(lean_object* v_none_29_){
_start:
{
lean_inc(v_none_29_);
return v_none_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg___boxed(lean_object* v_none_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Meta_Grind_CheckResult_none_elim___redArg(v_none_30_);
lean_dec(v_none_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_none_35_){
_start:
{
lean_inc(v_none_35_);
return v_none_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_none_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Lean_Meta_Grind_CheckResult_none_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_none_39_);
lean_dec(v_none_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(lean_object* v_progress_42_){
_start:
{
lean_inc(v_progress_42_);
return v_progress_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg___boxed(lean_object* v_progress_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(v_progress_43_);
lean_dec(v_progress_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_progress_48_){
_start:
{
lean_inc(v_progress_48_);
return v_progress_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_progress_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_Meta_Grind_CheckResult_progress_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_progress_52_);
lean_dec(v_progress_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(lean_object* v_propagated_55_){
_start:
{
lean_inc(v_propagated_55_);
return v_propagated_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg___boxed(lean_object* v_propagated_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(v_propagated_56_);
lean_dec(v_propagated_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_propagated_61_){
_start:
{
lean_inc(v_propagated_61_);
return v_propagated_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_propagated_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Lean_Meta_Grind_CheckResult_propagated_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_propagated_65_);
lean_dec(v_propagated_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(lean_object* v_closed_68_){
_start:
{
lean_inc(v_closed_68_);
return v_closed_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg___boxed(lean_object* v_closed_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(v_closed_69_);
lean_dec(v_closed_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_closed_74_){
_start:
{
lean_inc(v_closed_74_);
return v_closed_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_closed_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Lean_Meta_Grind_CheckResult_closed_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_closed_78_);
lean_dec(v_closed_78_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCheckResult_beq(uint8_t v_x_81_, uint8_t v_y_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_81_);
v___x_84_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_y_82_);
v___x_85_ = lean_nat_dec_eq(v___x_83_, v___x_84_);
lean_dec(v___x_84_);
lean_dec(v___x_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed(lean_object* v_x_86_, lean_object* v_y_87_){
_start:
{
uint8_t v_x_17__boxed_88_; uint8_t v_y_18__boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_x_17__boxed_88_ = lean_unbox(v_x_86_);
v_y_18__boxed_89_ = lean_unbox(v_y_87_);
v_res_90_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_x_17__boxed_88_, v_y_18__boxed_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedCheckResult_default(void){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedCheckResult(void){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(2u);
v___x_109_ = lean_nat_to_int(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr(uint8_t v_x_112_, lean_object* v_prec_113_){
_start:
{
lean_object* v___y_115_; lean_object* v___y_122_; lean_object* v___y_129_; lean_object* v___y_136_; 
switch(v_x_112_)
{
case 0:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_113_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_115_ = v___x_144_;
goto v___jp_114_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_115_ = v___x_145_;
goto v___jp_114_;
}
}
case 1:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1024u);
v___x_147_ = lean_nat_dec_le(v___x_146_, v_prec_113_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_122_ = v___x_148_;
goto v___jp_121_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_122_ = v___x_149_;
goto v___jp_121_;
}
}
case 2:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1024u);
v___x_151_ = lean_nat_dec_le(v___x_150_, v_prec_113_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_129_ = v___x_152_;
goto v___jp_128_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_129_ = v___x_153_;
goto v___jp_128_;
}
}
default: 
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1024u);
v___x_155_ = lean_nat_dec_le(v___x_154_, v_prec_113_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_136_ = v___x_156_;
goto v___jp_135_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_136_ = v___x_157_;
goto v___jp_135_;
}
}
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_116_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1));
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___y_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = l_Repr_addAppParen(v___x_119_, v_prec_113_);
return v___x_120_;
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3));
v___x_124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_124_, 0, v___y_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = 0;
v___x_126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_125_);
v___x_127_ = l_Repr_addAppParen(v___x_126_, v_prec_113_);
return v___x_127_;
}
v___jp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_130_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5));
v___x_131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_131_, 0, v___y_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = 0;
v___x_133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_132_);
v___x_134_ = l_Repr_addAppParen(v___x_133_, v_prec_113_);
return v___x_134_;
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7));
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_113_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___boxed(lean_object* v_x_158_, lean_object* v_prec_159_){
_start:
{
uint8_t v_x_233__boxed_160_; lean_object* v_res_161_; 
v_x_233__boxed_160_ = lean_unbox(v_x_158_);
v_res_161_ = l_Lean_Meta_Grind_instReprCheckResult_repr(v_x_233__boxed_160_, v_prec_159_);
lean_dec(v_prec_159_);
return v_res_161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_lt(uint8_t v_r_u2081_164_, uint8_t v_r_u2082_165_){
_start:
{
switch(v_r_u2082_165_)
{
case 0:
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
case 1:
{
switch(v_r_u2081_164_)
{
case 0:
{
uint8_t v___x_167_; 
v___x_167_ = 1;
return v___x_167_;
}
case 1:
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
case 2:
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
default: 
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
}
case 2:
{
switch(v_r_u2081_164_)
{
case 0:
{
uint8_t v___x_171_; 
v___x_171_ = 1;
return v___x_171_;
}
case 1:
{
uint8_t v___x_172_; 
v___x_172_ = 1;
return v___x_172_;
}
case 2:
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
default: 
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
}
}
default: 
{
if (v_r_u2081_164_ == 3)
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = 1;
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_lt___boxed(lean_object* v_r_u2081_177_, lean_object* v_r_u2082_178_){
_start:
{
uint8_t v_r_u2081_boxed_179_; uint8_t v_r_u2082_boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v_r_u2081_boxed_179_ = lean_unbox(v_r_u2081_177_);
v_r_u2082_boxed_180_ = lean_unbox(v_r_u2082_178_);
v_res_181_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_boxed_179_, v_r_u2082_boxed_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_le(uint8_t v_r_u2081_183_, uint8_t v_r_u2082_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_r_u2081_183_, v_r_u2082_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_183_, v_r_u2082_184_);
return v___x_186_;
}
else
{
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_le___boxed(lean_object* v_r_u2081_187_, lean_object* v_r_u2082_188_){
_start:
{
uint8_t v_r_u2081_boxed_189_; uint8_t v_r_u2082_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_r_u2081_boxed_189_ = lean_unbox(v_r_u2081_187_);
v_r_u2082_boxed_190_ = lean_unbox(v_r_u2082_188_);
v_res_191_ = l_Lean_Meta_Grind_CheckResult_le(v_r_u2081_boxed_189_, v_r_u2082_boxed_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_join(uint8_t v_r_u2081_193_, uint8_t v_r_u2082_194_){
_start:
{
switch(v_r_u2081_193_)
{
case 0:
{
return v_r_u2082_194_;
}
case 1:
{
switch(v_r_u2082_194_)
{
case 0:
{
return v_r_u2081_193_;
}
case 1:
{
return v_r_u2082_194_;
}
case 2:
{
return v_r_u2082_194_;
}
default: 
{
return v_r_u2082_194_;
}
}
}
case 2:
{
switch(v_r_u2082_194_)
{
case 0:
{
return v_r_u2081_193_;
}
case 1:
{
return v_r_u2081_193_;
}
case 2:
{
return v_r_u2082_194_;
}
default: 
{
return v_r_u2082_194_;
}
}
}
default: 
{
if (v_r_u2082_194_ == 3)
{
return v_r_u2082_194_;
}
else
{
return v_r_u2081_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_join___boxed(lean_object* v_r_u2081_195_, lean_object* v_r_u2082_196_){
_start:
{
uint8_t v_r_u2081_boxed_197_; uint8_t v_r_u2082_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_r_u2081_boxed_197_ = lean_unbox(v_r_u2081_195_);
v_r_u2082_boxed_198_ = lean_unbox(v_r_u2082_196_);
v_res_199_ = l_Lean_Meta_Grind_CheckResult_join(v_r_u2081_boxed_197_, v_r_u2082_boxed_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CheckResult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedCheckResult_default = _init_l_Lean_Meta_Grind_instInhabitedCheckResult_default();
l_Lean_Meta_Grind_instInhabitedCheckResult = _init_l_Lean_Meta_Grind_instInhabitedCheckResult();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_CheckResult(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CheckResult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CheckResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_CheckResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_CheckResult(builtin);
}
#ifdef __cplusplus
}
#endif
