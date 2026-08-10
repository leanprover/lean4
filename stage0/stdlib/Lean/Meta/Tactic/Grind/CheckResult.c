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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(lean_object* v_k_9_){
_start:
{
lean_inc(v_k_9_);
return v_k_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg___boxed(lean_object* v_k_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(v_k_10_);
lean_dec(v_k_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Meta_Grind_CheckResult_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg(lean_object* v_none_24_){
_start:
{
lean_inc(v_none_24_);
return v_none_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg___boxed(lean_object* v_none_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Grind_CheckResult_none_elim___redArg(v_none_25_);
lean_dec(v_none_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_none_30_){
_start:
{
lean_inc(v_none_30_);
return v_none_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___boxed(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_none_34_){
_start:
{
uint8_t v_t_boxed_35_; lean_object* v_res_36_; 
v_t_boxed_35_ = lean_unbox(v_t_32_);
v_res_36_ = l_Lean_Meta_Grind_CheckResult_none_elim(v_motive_31_, v_t_boxed_35_, v_h_33_, v_none_34_);
lean_dec(v_none_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(lean_object* v_progress_37_){
_start:
{
lean_inc(v_progress_37_);
return v_progress_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg___boxed(lean_object* v_progress_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(v_progress_38_);
lean_dec(v_progress_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim(lean_object* v_motive_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_progress_43_){
_start:
{
lean_inc(v_progress_43_);
return v_progress_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_progress_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Lean_Meta_Grind_CheckResult_progress_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_progress_47_);
lean_dec(v_progress_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(lean_object* v_propagated_50_){
_start:
{
lean_inc(v_propagated_50_);
return v_propagated_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg___boxed(lean_object* v_propagated_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(v_propagated_51_);
lean_dec(v_propagated_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_propagated_56_){
_start:
{
lean_inc(v_propagated_56_);
return v_propagated_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_propagated_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Lean_Meta_Grind_CheckResult_propagated_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_propagated_60_);
lean_dec(v_propagated_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(lean_object* v_closed_63_){
_start:
{
lean_inc(v_closed_63_);
return v_closed_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg___boxed(lean_object* v_closed_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(v_closed_64_);
lean_dec(v_closed_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim(lean_object* v_motive_66_, uint8_t v_t_67_, lean_object* v_h_68_, lean_object* v_closed_69_){
_start:
{
lean_inc(v_closed_69_);
return v_closed_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_closed_73_){
_start:
{
uint8_t v_t_boxed_74_; lean_object* v_res_75_; 
v_t_boxed_74_ = lean_unbox(v_t_71_);
v_res_75_ = l_Lean_Meta_Grind_CheckResult_closed_elim(v_motive_70_, v_t_boxed_74_, v_h_72_, v_closed_73_);
lean_dec(v_closed_73_);
return v_res_75_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCheckResult_beq(uint8_t v_x_76_, uint8_t v_y_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_76_);
v___x_79_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_y_77_);
v___x_80_ = lean_nat_dec_eq(v___x_78_, v___x_79_);
lean_dec(v___x_79_);
lean_dec(v___x_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v_x_17__boxed_83_; uint8_t v_y_18__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_x_17__boxed_83_ = lean_unbox(v_x_81_);
v_y_18__boxed_84_ = lean_unbox(v_y_82_);
v_res_85_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_x_17__boxed_83_, v_y_18__boxed_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedCheckResult_default(void){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedCheckResult(void){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(2u);
v___x_104_ = lean_nat_to_int(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_to_int(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr(uint8_t v_x_107_, lean_object* v_prec_108_){
_start:
{
lean_object* v___y_110_; lean_object* v___y_117_; lean_object* v___y_124_; lean_object* v___y_131_; 
switch(v_x_107_)
{
case 0:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1024u);
v___x_138_ = lean_nat_dec_le(v___x_137_, v_prec_108_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_110_ = v___x_139_;
goto v___jp_109_;
}
else
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_110_ = v___x_140_;
goto v___jp_109_;
}
}
case 1:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = lean_nat_dec_le(v___x_141_, v_prec_108_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_117_ = v___x_143_;
goto v___jp_116_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_117_ = v___x_144_;
goto v___jp_116_;
}
}
case 2:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(1024u);
v___x_146_ = lean_nat_dec_le(v___x_145_, v_prec_108_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_124_ = v___x_147_;
goto v___jp_123_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_124_ = v___x_148_;
goto v___jp_123_;
}
}
default: 
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1024u);
v___x_150_ = lean_nat_dec_le(v___x_149_, v_prec_108_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_131_ = v___x_151_;
goto v___jp_130_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_131_ = v___x_152_;
goto v___jp_130_;
}
}
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1));
lean_inc(v___y_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___y_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_prec_108_);
return v___x_115_;
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3));
lean_inc(v___y_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v_prec_108_);
return v___x_122_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5));
lean_inc(v___y_124_);
v___x_126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_126_, 0, v___y_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = 0;
v___x_128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_127_);
v___x_129_ = l_Repr_addAppParen(v___x_128_, v_prec_108_);
return v___x_129_;
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7));
lean_inc(v___y_131_);
v___x_133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_133_, 0, v___y_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_prec_108_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___boxed(lean_object* v_x_153_, lean_object* v_prec_154_){
_start:
{
uint8_t v_x_233__boxed_155_; lean_object* v_res_156_; 
v_x_233__boxed_155_ = lean_unbox(v_x_153_);
v_res_156_ = l_Lean_Meta_Grind_instReprCheckResult_repr(v_x_233__boxed_155_, v_prec_154_);
lean_dec(v_prec_154_);
return v_res_156_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_lt(uint8_t v_r_u2081_159_, uint8_t v_r_u2082_160_){
_start:
{
switch(v_r_u2082_160_)
{
case 0:
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
case 1:
{
switch(v_r_u2081_159_)
{
case 0:
{
uint8_t v___x_162_; 
v___x_162_ = 1;
return v___x_162_;
}
case 1:
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
case 2:
{
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
default: 
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
}
}
case 2:
{
switch(v_r_u2081_159_)
{
case 0:
{
uint8_t v___x_166_; 
v___x_166_ = 1;
return v___x_166_;
}
case 1:
{
uint8_t v___x_167_; 
v___x_167_ = 1;
return v___x_167_;
}
case 2:
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
default: 
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
}
}
default: 
{
if (v_r_u2081_159_ == 3)
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 1;
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_lt___boxed(lean_object* v_r_u2081_172_, lean_object* v_r_u2082_173_){
_start:
{
uint8_t v_r_u2081_boxed_174_; uint8_t v_r_u2082_boxed_175_; uint8_t v_res_176_; lean_object* v_r_177_; 
v_r_u2081_boxed_174_ = lean_unbox(v_r_u2081_172_);
v_r_u2082_boxed_175_ = lean_unbox(v_r_u2082_173_);
v_res_176_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_boxed_174_, v_r_u2082_boxed_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_le(uint8_t v_r_u2081_178_, uint8_t v_r_u2082_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_r_u2081_178_, v_r_u2082_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_178_, v_r_u2082_179_);
return v___x_181_;
}
else
{
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_le___boxed(lean_object* v_r_u2081_182_, lean_object* v_r_u2082_183_){
_start:
{
uint8_t v_r_u2081_boxed_184_; uint8_t v_r_u2082_boxed_185_; uint8_t v_res_186_; lean_object* v_r_187_; 
v_r_u2081_boxed_184_ = lean_unbox(v_r_u2081_182_);
v_r_u2082_boxed_185_ = lean_unbox(v_r_u2082_183_);
v_res_186_ = l_Lean_Meta_Grind_CheckResult_le(v_r_u2081_boxed_184_, v_r_u2082_boxed_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_join(uint8_t v_r_u2081_188_, uint8_t v_r_u2082_189_){
_start:
{
switch(v_r_u2081_188_)
{
case 0:
{
return v_r_u2082_189_;
}
case 1:
{
switch(v_r_u2082_189_)
{
case 0:
{
return v_r_u2081_188_;
}
case 1:
{
return v_r_u2082_189_;
}
case 2:
{
return v_r_u2082_189_;
}
default: 
{
return v_r_u2082_189_;
}
}
}
case 2:
{
switch(v_r_u2082_189_)
{
case 0:
{
return v_r_u2081_188_;
}
case 1:
{
return v_r_u2081_188_;
}
case 2:
{
return v_r_u2082_189_;
}
default: 
{
return v_r_u2082_189_;
}
}
}
default: 
{
if (v_r_u2082_189_ == 3)
{
return v_r_u2082_189_;
}
else
{
return v_r_u2081_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_join___boxed(lean_object* v_r_u2081_190_, lean_object* v_r_u2082_191_){
_start:
{
uint8_t v_r_u2081_boxed_192_; uint8_t v_r_u2082_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_r_u2081_boxed_192_ = lean_unbox(v_r_u2081_190_);
v_r_u2082_boxed_193_ = lean_unbox(v_r_u2082_191_);
v_res_194_ = l_Lean_Meta_Grind_CheckResult_join(v_r_u2081_boxed_192_, v_r_u2082_boxed_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CheckResult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
