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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_Grind_CheckResult_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_Grind_CheckResult_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg(lean_object* v_none_22_){
_start:
{
lean_inc(v_none_22_);
return v_none_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___redArg___boxed(lean_object* v_none_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Grind_CheckResult_none_elim___redArg(v_none_23_);
lean_dec(v_none_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_none_28_){
_start:
{
lean_inc(v_none_28_);
return v_none_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_none_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_Grind_CheckResult_none_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_none_32_);
lean_dec(v_none_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(lean_object* v_progress_35_){
_start:
{
lean_inc(v_progress_35_);
return v_progress_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg___boxed(lean_object* v_progress_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(v_progress_36_);
lean_dec(v_progress_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_progress_41_){
_start:
{
lean_inc(v_progress_41_);
return v_progress_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_progress_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_Grind_CheckResult_progress_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_progress_45_);
lean_dec(v_progress_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(lean_object* v_propagated_48_){
_start:
{
lean_inc(v_propagated_48_);
return v_propagated_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg___boxed(lean_object* v_propagated_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(v_propagated_49_);
lean_dec(v_propagated_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_propagated_54_){
_start:
{
lean_inc(v_propagated_54_);
return v_propagated_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_propagated_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_Grind_CheckResult_propagated_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_propagated_58_);
lean_dec(v_propagated_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(lean_object* v_closed_61_){
_start:
{
lean_inc(v_closed_61_);
return v_closed_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg___boxed(lean_object* v_closed_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(v_closed_62_);
lean_dec(v_closed_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_closed_67_){
_start:
{
lean_inc(v_closed_67_);
return v_closed_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_closed_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Meta_Grind_CheckResult_closed_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_closed_71_);
lean_dec(v_closed_71_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCheckResult_beq(uint8_t v_x_74_, uint8_t v_y_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_76_ = lean_box(v_x_74_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_box(v_y_75_);
v___x_79_ = lean_obj_tag_nat(v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v_x_24__boxed_83_; uint8_t v_y_25__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_x_24__boxed_83_ = lean_unbox(v_x_81_);
v_y_25__boxed_84_ = lean_unbox(v_y_82_);
v_res_85_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_x_24__boxed_83_, v_y_25__boxed_84_);
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
uint8_t v_x_225__boxed_155_; lean_object* v_res_156_; 
v_x_225__boxed_155_ = lean_unbox(v_x_153_);
v_res_156_ = l_Lean_Meta_Grind_instReprCheckResult_repr(v_x_225__boxed_155_, v_prec_154_);
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
if (v_r_u2081_159_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 1;
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
}
case 2:
{
switch(v_r_u2081_159_)
{
case 0:
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
case 1:
{
uint8_t v___x_165_; 
v___x_165_ = 1;
return v___x_165_;
}
default: 
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
}
}
default: 
{
if (v_r_u2081_159_ == 3)
{
uint8_t v___x_167_; 
v___x_167_ = 0;
return v___x_167_;
}
else
{
uint8_t v___x_168_; 
v___x_168_ = 1;
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_lt___boxed(lean_object* v_r_u2081_169_, lean_object* v_r_u2082_170_){
_start:
{
uint8_t v_r_u2081_boxed_171_; uint8_t v_r_u2082_boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_r_u2081_boxed_171_ = lean_unbox(v_r_u2081_169_);
v_r_u2082_boxed_172_ = lean_unbox(v_r_u2082_170_);
v_res_173_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_boxed_171_, v_r_u2082_boxed_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_le(uint8_t v_r_u2081_175_, uint8_t v_r_u2082_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_r_u2081_175_, v_r_u2082_176_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_175_, v_r_u2082_176_);
return v___x_178_;
}
else
{
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_le___boxed(lean_object* v_r_u2081_179_, lean_object* v_r_u2082_180_){
_start:
{
uint8_t v_r_u2081_boxed_181_; uint8_t v_r_u2082_boxed_182_; uint8_t v_res_183_; lean_object* v_r_184_; 
v_r_u2081_boxed_181_ = lean_unbox(v_r_u2081_179_);
v_r_u2082_boxed_182_ = lean_unbox(v_r_u2082_180_);
v_res_183_ = l_Lean_Meta_Grind_CheckResult_le(v_r_u2081_boxed_181_, v_r_u2082_boxed_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_CheckResult_join(uint8_t v_r_u2081_185_, uint8_t v_r_u2082_186_){
_start:
{
switch(v_r_u2081_185_)
{
case 0:
{
return v_r_u2082_186_;
}
case 1:
{
if (v_r_u2082_186_ == 0)
{
return v_r_u2081_185_;
}
else
{
return v_r_u2082_186_;
}
}
case 2:
{
switch(v_r_u2082_186_)
{
case 0:
{
return v_r_u2081_185_;
}
case 1:
{
return v_r_u2081_185_;
}
default: 
{
return v_r_u2082_186_;
}
}
}
default: 
{
if (v_r_u2082_186_ == 3)
{
return v_r_u2082_186_;
}
else
{
return v_r_u2081_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_join___boxed(lean_object* v_r_u2081_187_, lean_object* v_r_u2082_188_){
_start:
{
uint8_t v_r_u2081_boxed_189_; uint8_t v_r_u2082_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_r_u2081_boxed_189_ = lean_unbox(v_r_u2081_187_);
v_r_u2082_boxed_190_ = lean_unbox(v_r_u2082_188_);
v_res_191_ = l_Lean_Meta_Grind_CheckResult_join(v_r_u2081_boxed_189_, v_r_u2082_boxed_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
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
