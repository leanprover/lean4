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
lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Meta_Grind_CheckResult_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_Grind_CheckResult_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_Grind_CheckResult_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Meta_Grind_CheckResult_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
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
lean_object* l_Lean_Meta_Grind_CheckResult_none_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_none_30_){
_start:
{
lean_inc(v_none_30_);
return v_none_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_none_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_Grind_CheckResult_none_elim(lean_box(0), v_t_28_, lean_box(0), v_none_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_none_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_none_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_Grind_CheckResult_none_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_none_35_);
lean_dec(v_none_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(lean_object* v_progress_38_){
_start:
{
lean_inc(v_progress_38_);
return v_progress_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___redArg___boxed(lean_object* v_progress_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(v_progress_39_);
lean_dec(v_progress_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_progress_44_){
_start:
{
lean_inc(v_progress_44_);
return v_progress_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_progress_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_progress_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_Grind_CheckResult_progress_elim(lean_box(0), v_t_42_, lean_box(0), v_progress_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_progress_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_progress_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_Grind_CheckResult_progress_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_progress_49_);
lean_dec(v_progress_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(lean_object* v_propagated_52_){
_start:
{
lean_inc(v_propagated_52_);
return v_propagated_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg___boxed(lean_object* v_propagated_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(v_propagated_53_);
lean_dec(v_propagated_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_propagated_58_){
_start:
{
lean_inc(v_propagated_58_);
return v_propagated_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_propagated_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_propagated_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_Grind_CheckResult_propagated_elim(lean_box(0), v_t_56_, lean_box(0), v_propagated_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_propagated_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_propagated_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Meta_Grind_CheckResult_propagated_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_propagated_63_);
lean_dec(v_propagated_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(lean_object* v_closed_66_){
_start:
{
lean_inc(v_closed_66_);
return v_closed_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___redArg___boxed(lean_object* v_closed_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(v_closed_67_);
lean_dec(v_closed_67_);
return v_res_68_;
}
}
lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_closed_72_){
_start:
{
lean_inc(v_closed_72_);
return v_closed_72_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_closed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_closed_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Meta_Grind_CheckResult_closed_elim(lean_box(0), v_t_70_, lean_box(0), v_closed_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_closed_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_closed_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Lean_Meta_Grind_CheckResult_closed_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_closed_77_);
lean_dec(v_closed_77_);
return v_res_79_;
}
}
uint8_t l_Lean_Meta_Grind_instBEqCheckResult_beq(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_82_ = lean_box(v_x_80_);
v___x_83_ = lean_obj_tag_nat(v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = lean_box(v_y_81_);
v___x_85_ = lean_obj_tag_nat(v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_nat_dec_eq(v___x_83_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqCheckResult_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_80_ = stack[0].m_num;
uint8_t v_y_81_ = stack[1].m_num;
uint8_t v_res_87_;
v_res_87_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_x_80_, v_y_81_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed(lean_object* v_x_88_, lean_object* v_y_89_){
_start:
{
uint8_t v_x_24__boxed_90_; uint8_t v_y_25__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_24__boxed_90_ = lean_unbox(v_x_88_);
v_y_25__boxed_91_ = lean_unbox(v_y_89_);
v_res_92_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_x_24__boxed_90_, v_y_25__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedCheckResult_default(void){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedCheckResult(void){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(2u);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr(uint8_t v_x_114_, lean_object* v_prec_115_){
_start:
{
lean_object* v___y_117_; lean_object* v___y_124_; lean_object* v___y_131_; lean_object* v___y_138_; 
switch(v_x_114_)
{
case 0:
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1024u);
v___x_145_ = lean_nat_dec_le(v___x_144_, v_prec_115_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_117_ = v___x_146_;
goto v___jp_116_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_117_ = v___x_147_;
goto v___jp_116_;
}
}
case 1:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1024u);
v___x_149_ = lean_nat_dec_le(v___x_148_, v_prec_115_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_124_ = v___x_150_;
goto v___jp_123_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_124_ = v___x_151_;
goto v___jp_123_;
}
}
case 2:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_prec_115_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_131_ = v___x_154_;
goto v___jp_130_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_131_ = v___x_155_;
goto v___jp_130_;
}
}
default: 
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1024u);
v___x_157_ = lean_nat_dec_le(v___x_156_, v_prec_115_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8);
v___y_138_ = v___x_158_;
goto v___jp_137_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9, &l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once, _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9);
v___y_138_ = v___x_159_;
goto v___jp_137_;
}
}
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1));
lean_inc(v___y_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v_prec_115_);
return v___x_122_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3));
lean_inc(v___y_124_);
v___x_126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_126_, 0, v___y_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = 0;
v___x_128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_127_);
v___x_129_ = l_Repr_addAppParen(v___x_128_, v_prec_115_);
return v___x_129_;
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5));
lean_inc(v___y_131_);
v___x_133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_133_, 0, v___y_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_prec_115_);
return v___x_136_;
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7));
lean_inc(v___y_138_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_115_);
return v___x_143_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instReprCheckResult_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_114_ = stack[0].m_num;
lean_object* v_prec_115_ = stack[1].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_Lean_Meta_Grind_instReprCheckResult_repr(v_x_114_, v_prec_115_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCheckResult_repr___boxed(lean_object* v_x_161_, lean_object* v_prec_162_){
_start:
{
uint8_t v_x_225__boxed_163_; lean_object* v_res_164_; 
v_x_225__boxed_163_ = lean_unbox(v_x_161_);
v_res_164_ = l_Lean_Meta_Grind_instReprCheckResult_repr(v_x_225__boxed_163_, v_prec_162_);
lean_dec(v_prec_162_);
return v_res_164_;
}
}
uint8_t l_Lean_Meta_Grind_CheckResult_lt(uint8_t v_r_u2081_167_, uint8_t v_r_u2082_168_){
_start:
{
switch(v_r_u2082_168_)
{
case 0:
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
case 1:
{
if (v_r_u2081_167_ == 0)
{
uint8_t v___x_170_; 
v___x_170_ = 1;
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
case 2:
{
switch(v_r_u2081_167_)
{
case 0:
{
uint8_t v___x_172_; 
v___x_172_ = 1;
return v___x_172_;
}
case 1:
{
uint8_t v___x_173_; 
v___x_173_ = 1;
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
if (v_r_u2081_167_ == 3)
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
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_lt_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_u2081_167_ = stack[0].m_num;
uint8_t v_r_u2082_168_ = stack[1].m_num;
uint8_t v_res_177_;
v_res_177_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_167_, v_r_u2082_168_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_lt___boxed(lean_object* v_r_u2081_178_, lean_object* v_r_u2082_179_){
_start:
{
uint8_t v_r_u2081_boxed_180_; uint8_t v_r_u2082_boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_r_u2081_boxed_180_ = lean_unbox(v_r_u2081_178_);
v_r_u2082_boxed_181_ = lean_unbox(v_r_u2082_179_);
v_res_182_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_boxed_180_, v_r_u2082_boxed_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
uint8_t l_Lean_Meta_Grind_CheckResult_le(uint8_t v_r_u2081_184_, uint8_t v_r_u2082_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_r_u2081_184_, v_r_u2082_185_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
v___x_187_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_184_, v_r_u2082_185_);
return v___x_187_;
}
else
{
return v___x_186_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_le_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_u2081_184_ = stack[0].m_num;
uint8_t v_r_u2082_185_ = stack[1].m_num;
uint8_t v_res_188_;
v_res_188_ = l_Lean_Meta_Grind_CheckResult_le(v_r_u2081_184_, v_r_u2082_185_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_le___boxed(lean_object* v_r_u2081_189_, lean_object* v_r_u2082_190_){
_start:
{
uint8_t v_r_u2081_boxed_191_; uint8_t v_r_u2082_boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_r_u2081_boxed_191_ = lean_unbox(v_r_u2081_189_);
v_r_u2082_boxed_192_ = lean_unbox(v_r_u2082_190_);
v_res_193_ = l_Lean_Meta_Grind_CheckResult_le(v_r_u2081_boxed_191_, v_r_u2082_boxed_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
uint8_t l_Lean_Meta_Grind_CheckResult_join(uint8_t v_r_u2081_195_, uint8_t v_r_u2082_196_){
_start:
{
switch(v_r_u2081_195_)
{
case 0:
{
return v_r_u2082_196_;
}
case 1:
{
if (v_r_u2082_196_ == 0)
{
return v_r_u2081_195_;
}
else
{
return v_r_u2082_196_;
}
}
case 2:
{
switch(v_r_u2082_196_)
{
case 0:
{
return v_r_u2081_195_;
}
case 1:
{
return v_r_u2081_195_;
}
default: 
{
return v_r_u2082_196_;
}
}
}
default: 
{
if (v_r_u2082_196_ == 3)
{
return v_r_u2082_196_;
}
else
{
return v_r_u2081_195_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CheckResult_join_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_u2081_195_ = stack[0].m_num;
uint8_t v_r_u2082_196_ = stack[1].m_num;
uint8_t v_res_197_;
v_res_197_ = l_Lean_Meta_Grind_CheckResult_join(v_r_u2081_195_, v_r_u2082_196_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CheckResult_join___boxed(lean_object* v_r_u2081_198_, lean_object* v_r_u2082_199_){
_start:
{
uint8_t v_r_u2081_boxed_200_; uint8_t v_r_u2082_boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_r_u2081_boxed_200_ = lean_unbox(v_r_u2081_198_);
v_r_u2082_boxed_201_ = lean_unbox(v_r_u2082_199_);
v_res_202_ = l_Lean_Meta_Grind_CheckResult_join(v_r_u2081_boxed_200_, v_r_u2082_boxed_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
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
