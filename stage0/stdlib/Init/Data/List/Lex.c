// Lean compiler output
// Module: Init.Data.List.Lex
// Imports: import Init.Data.Order.Lemmas public import Init.Data.BEq public import Init.Data.Order.Classes public import Init.Ext public import Init.NotationExtra import Init.ByCases import Init.Data.Bool import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas import Init.TacticsExtra
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
LEAN_EXPORT lean_object* l_List_instTransLt___redArg();
LEAN_EXPORT lean_object* l_List_instTransLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg();
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_isEqv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_isEqv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instTransLt___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_List_instTransLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_List_instTransLt___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_List_instTransLt___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_List_instTransLt___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLt(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT void l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_12_;
v_res_12_ = l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg();
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(lean_object* v_l_u2081_21_, lean_object* v_l_u2082_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_, lean_object* v_h__3_25_){
_start:
{
if (lean_obj_tag(v_l_u2081_21_) == 0)
{
lean_dec(v_h__3_25_);
if (lean_obj_tag(v_l_u2082_22_) == 0)
{
lean_object* v___x_26_; 
lean_dec(v_h__1_23_);
v___x_26_ = lean_apply_1(v_h__2_24_, v_l_u2082_22_);
return v___x_26_;
}
else
{
lean_object* v_head_27_; lean_object* v_tail_28_; lean_object* v___x_29_; 
lean_dec(v_h__2_24_);
v_head_27_ = lean_ctor_get(v_l_u2082_22_, 0);
lean_inc(v_head_27_);
v_tail_28_ = lean_ctor_get(v_l_u2082_22_, 1);
lean_inc(v_tail_28_);
lean_dec_ref_known(v_l_u2082_22_, 2);
v___x_29_ = lean_apply_2(v_h__1_23_, v_head_27_, v_tail_28_);
return v___x_29_;
}
}
else
{
lean_dec(v_h__1_23_);
if (lean_obj_tag(v_l_u2082_22_) == 0)
{
lean_object* v___x_30_; 
lean_dec(v_h__3_25_);
v___x_30_ = lean_apply_1(v_h__2_24_, v_l_u2081_21_);
return v___x_30_;
}
else
{
lean_object* v_head_31_; lean_object* v_tail_32_; lean_object* v_head_33_; lean_object* v_tail_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_24_);
v_head_31_ = lean_ctor_get(v_l_u2081_21_, 0);
lean_inc(v_head_31_);
v_tail_32_ = lean_ctor_get(v_l_u2081_21_, 1);
lean_inc(v_tail_32_);
lean_dec_ref_known(v_l_u2081_21_, 2);
v_head_33_ = lean_ctor_get(v_l_u2082_22_, 0);
lean_inc(v_head_33_);
v_tail_34_ = lean_ctor_get(v_l_u2082_22_, 1);
lean_inc(v_tail_34_);
lean_dec_ref_known(v_l_u2082_22_, 2);
v___x_35_ = lean_apply_4(v_h__3_25_, v_head_31_, v_tail_32_, v_head_33_, v_tail_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(lean_object* v_00_u03b1_36_, lean_object* v_motive_37_, lean_object* v_l_u2081_38_, lean_object* v_l_u2082_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_, lean_object* v_h__3_42_){
_start:
{
if (lean_obj_tag(v_l_u2081_38_) == 0)
{
lean_dec(v_h__3_42_);
if (lean_obj_tag(v_l_u2082_39_) == 0)
{
lean_object* v___x_43_; 
lean_dec(v_h__1_40_);
v___x_43_ = lean_apply_1(v_h__2_41_, v_l_u2082_39_);
return v___x_43_;
}
else
{
lean_object* v_head_44_; lean_object* v_tail_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_41_);
v_head_44_ = lean_ctor_get(v_l_u2082_39_, 0);
lean_inc(v_head_44_);
v_tail_45_ = lean_ctor_get(v_l_u2082_39_, 1);
lean_inc(v_tail_45_);
lean_dec_ref_known(v_l_u2082_39_, 2);
v___x_46_ = lean_apply_2(v_h__1_40_, v_head_44_, v_tail_45_);
return v___x_46_;
}
}
else
{
lean_dec(v_h__1_40_);
if (lean_obj_tag(v_l_u2082_39_) == 0)
{
lean_object* v___x_47_; 
lean_dec(v_h__3_42_);
v___x_47_ = lean_apply_1(v_h__2_41_, v_l_u2081_38_);
return v___x_47_;
}
else
{
lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_41_);
v_head_48_ = lean_ctor_get(v_l_u2081_38_, 0);
lean_inc(v_head_48_);
v_tail_49_ = lean_ctor_get(v_l_u2081_38_, 1);
lean_inc(v_tail_49_);
lean_dec_ref_known(v_l_u2081_38_, 2);
v_head_50_ = lean_ctor_get(v_l_u2082_39_, 0);
lean_inc(v_head_50_);
v_tail_51_ = lean_ctor_get(v_l_u2082_39_, 1);
lean_inc(v_tail_51_);
lean_dec_ref_known(v_l_u2082_39_, 2);
v___x_52_ = lean_apply_4(v_h__3_42_, v_head_48_, v_tail_49_, v_head_50_, v_tail_51_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_isEqv_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_dec(v_h__2_57_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_59_; 
lean_dec(v_h__3_58_);
v___x_59_ = lean_apply_1(v_h__1_56_, v_x_55_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
lean_dec(v_h__1_56_);
v___x_60_ = lean_apply_5(v_h__3_58_, v_x_53_, v_x_54_, v_x_55_, lean_box(0), lean_box(0));
return v___x_60_;
}
}
else
{
lean_dec(v_h__1_56_);
if (lean_obj_tag(v_x_54_) == 1)
{
lean_object* v_head_61_; lean_object* v_tail_62_; lean_object* v_head_63_; lean_object* v_tail_64_; lean_object* v___x_65_; 
lean_dec(v_h__3_58_);
v_head_61_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_61_);
v_tail_62_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_tail_62_);
lean_dec_ref_known(v_x_53_, 2);
v_head_63_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_63_);
v_tail_64_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_tail_64_);
lean_dec_ref_known(v_x_54_, 2);
v___x_65_ = lean_apply_5(v_h__2_57_, v_head_61_, v_tail_62_, v_head_63_, v_tail_64_, v_x_55_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
lean_dec(v_h__2_57_);
v___x_66_ = lean_apply_5(v_h__3_58_, v_x_53_, v_x_54_, v_x_55_, lean_box(0), lean_box(0));
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_isEqv_match__1_splitter(lean_object* v_00_u03b1_67_, lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_dec(v_h__2_73_);
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_75_; 
lean_dec(v_h__3_74_);
v___x_75_ = lean_apply_1(v_h__1_72_, v_x_71_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
lean_dec(v_h__1_72_);
v___x_76_ = lean_apply_5(v_h__3_74_, v_x_69_, v_x_70_, v_x_71_, lean_box(0), lean_box(0));
return v___x_76_;
}
}
else
{
lean_dec(v_h__1_72_);
if (lean_obj_tag(v_x_70_) == 1)
{
lean_object* v_head_77_; lean_object* v_tail_78_; lean_object* v_head_79_; lean_object* v_tail_80_; lean_object* v___x_81_; 
lean_dec(v_h__3_74_);
v_head_77_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_77_);
v_tail_78_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_tail_78_);
lean_dec_ref_known(v_x_69_, 2);
v_head_79_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_head_79_);
v_tail_80_ = lean_ctor_get(v_x_70_, 1);
lean_inc(v_tail_80_);
lean_dec_ref_known(v_x_70_, 2);
v___x_81_ = lean_apply_5(v_h__2_73_, v_head_77_, v_tail_78_, v_head_79_, v_tail_80_, v_x_71_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; 
lean_dec(v_h__2_73_);
v___x_82_ = lean_apply_5(v_h__3_74_, v_x_69_, v_x_70_, v_x_71_, lean_box(0), lean_box(0));
return v___x_82_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Lex(builtin);
}
#ifdef __cplusplus
}
#endif
