// Lean compiler output
// Module: Init.Data.List.ToArray
// Imports: import all Init.Data.List.Control public import Init.Data.List.Monadic import all Init.Data.Array.Basic import all Init.Data.Array.Set import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Bool import Init.Data.List.Erase import Init.Data.List.Find import Init.Data.List.Nat.Erase import Init.Data.List.Nat.InsertIdx import Init.Data.List.Nat.TakeDrop import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.List.Zip import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas import Init.Omega import Init.TacticsExtra
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* v_i_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_i_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* v_i_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_i_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(lean_object* v_00_u03b1_14_, lean_object* v_as_15_, lean_object* v_motive_16_, lean_object* v_i_17_, lean_object* v_h_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(v_i_17_, v_h__1_19_, v_h__2_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_as_23_, lean_object* v_motive_24_, lean_object* v_i_25_, lean_object* v_h_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_22_, v_as_23_, v_motive_24_, v_i_25_, v_h_26_, v_h__1_27_, v_h__2_28_);
lean_dec(v_i_25_);
lean_dec_ref(v_as_23_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object* v_____do__lift_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (lean_obj_tag(v_____do__lift_30_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_32_);
v_a_33_ = lean_ctor_get(v_____do__lift_30_, 0);
lean_inc(v_a_33_);
lean_dec_ref(v_____do__lift_30_);
v___x_34_ = lean_apply_1(v_h__1_31_, v_a_33_);
return v___x_34_;
}
else
{
lean_object* v_a_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_31_);
v_a_35_ = lean_ctor_get(v_____do__lift_30_, 0);
lean_inc(v_a_35_);
lean_dec_ref(v_____do__lift_30_);
v___x_36_ = lean_apply_1(v_h__2_32_, v_a_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object* v_00_u03b2_37_, lean_object* v_motive_38_, lean_object* v_____do__lift_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(v_____do__lift_39_, v_h__1_40_, v_h__2_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_45_);
v_a_46_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_a_46_);
lean_dec_ref(v_x_43_);
v___x_47_ = lean_apply_1(v_h__1_44_, v_a_46_);
return v___x_47_;
}
else
{
lean_object* v_a_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_44_);
v_a_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v_x_43_);
v___x_49_ = lean_apply_1(v_h__2_45_, v_a_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_52_, v_h__1_53_, v_h__2_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
if (lean_obj_tag(v_____do__lift_56_) == 1)
{
lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_58_);
v_val_59_ = lean_ctor_get(v_____do__lift_56_, 0);
lean_inc(v_val_59_);
lean_dec_ref(v_____do__lift_56_);
v___x_60_ = lean_apply_1(v_h__1_57_, v_val_59_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
lean_dec(v_h__1_57_);
v___x_61_ = lean_apply_2(v_h__2_58_, v_____do__lift_56_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_62_, lean_object* v_motive_63_, lean_object* v_____do__lift_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
if (lean_obj_tag(v_____do__lift_64_) == 1)
{
lean_object* v_val_67_; lean_object* v___x_68_; 
lean_dec(v_h__2_66_);
v_val_67_ = lean_ctor_get(v_____do__lift_64_, 0);
lean_inc(v_val_67_);
lean_dec_ref(v_____do__lift_64_);
v___x_68_ = lean_apply_1(v_h__1_65_, v_val_67_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; 
lean_dec(v_h__1_65_);
v___x_69_ = lean_apply_2(v_h__2_66_, v_____do__lift_64_, lean_box(0));
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_71_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__2_72_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_76_; 
lean_dec(v_h__2_72_);
v_val_75_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v_x_70_);
v___x_76_ = lean_apply_1(v_h__1_71_, v_val_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_77_, lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(v_x_79_, v_h__1_80_, v_h__2_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_85_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__1_84_, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_84_);
v_head_88_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_head_88_);
v_tail_89_ = lean_ctor_get(v_x_83_, 1);
lean_inc(v_tail_89_);
lean_dec_ref(v_x_83_);
v___x_90_ = lean_apply_2(v_h__2_85_, v_head_88_, v_tail_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_91_, lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(v_x_93_, v_h__1_94_, v_h__2_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
if (lean_obj_tag(v_____do__lift_97_) == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__1_98_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__2_99_, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; 
lean_dec(v_h__2_99_);
v_val_102_ = lean_ctor_get(v_____do__lift_97_, 0);
lean_inc(v_val_102_);
lean_dec_ref(v_____do__lift_97_);
v___x_103_ = lean_apply_1(v_h__1_98_, v_val_102_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_104_, lean_object* v_motive_105_, lean_object* v_____do__lift_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(v_____do__lift_106_, v_h__1_107_, v_h__2_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
lean_object* v_zero_113_; uint8_t v_isZero_114_; 
v_zero_113_ = lean_unsigned_to_nat(0u);
v_isZero_114_ = lean_nat_dec_eq(v_x_110_, v_zero_113_);
if (v_isZero_114_ == 1)
{
lean_object* v___x_115_; 
lean_dec(v_h__2_112_);
v___x_115_ = lean_apply_1(v_h__1_111_, lean_box(0));
return v___x_115_;
}
else
{
lean_object* v_one_116_; lean_object* v_n_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_111_);
v_one_116_ = lean_unsigned_to_nat(1u);
v_n_117_ = lean_nat_sub(v_x_110_, v_one_116_);
v___x_118_ = lean_apply_2(v_h__2_112_, v_n_117_, lean_box(0));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(v_x_119_, v_h__1_120_, v_h__2_121_);
lean_dec(v_x_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_123_, lean_object* v_xs_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(v_x_126_, v_h__1_128_, v_h__2_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_131_, lean_object* v_xs_132_, lean_object* v_motive_133_, lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_131_, v_xs_132_, v_motive_133_, v_x_134_, v_x_135_, v_h__1_136_, v_h__2_137_);
lean_dec(v_x_134_);
lean_dec_ref(v_xs_132_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* v_r_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
if (lean_obj_tag(v_r_139_) == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_140_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_h__2_141_, v___x_142_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_145_; 
lean_dec(v_h__2_141_);
v_val_144_ = lean_ctor_get(v_r_139_, 0);
lean_inc(v_val_144_);
lean_dec_ref(v_r_139_);
v___x_145_ = lean_apply_1(v_h__1_140_, v_val_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* v_00_u03b2_146_, lean_object* v_motive_147_, lean_object* v_r_148_, lean_object* v_h__1_149_, lean_object* v_h__2_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(v_r_148_, v_h__1_149_, v_h__2_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__2_154_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__1_153_, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_153_);
v_head_157_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_head_157_);
v_tail_158_ = lean_ctor_get(v_x_152_, 1);
lean_inc(v_tail_158_);
lean_dec_ref(v_x_152_);
v___x_159_ = lean_apply_2(v_h__2_154_, v_head_157_, v_tail_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(lean_object* v_00_u03b1_160_, lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(v_x_162_, v_h__1_163_, v_h__2_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_){
_start:
{
if (v_____do__lift_166_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_167_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_apply_1(v_h__2_168_, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_h__2_168_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_1(v_h__1_167_, v___x_171_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
uint8_t v_____do__lift_22__boxed_176_; lean_object* v_res_177_; 
v_____do__lift_22__boxed_176_ = lean_unbox(v_____do__lift_173_);
v_res_177_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_22__boxed_176_, v_h__1_174_, v_h__2_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object* v_motive_178_, uint8_t v_____do__lift_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_179_, v_h__1_180_, v_h__2_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_183_, lean_object* v_____do__lift_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
uint8_t v_____do__lift_33__boxed_187_; lean_object* v_res_188_; 
v_____do__lift_33__boxed_187_ = lean_unbox(v_____do__lift_184_);
v_res_188_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(v_motive_183_, v_____do__lift_33__boxed_187_, v_h__1_185_, v_h__2_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v_h__2_191_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_apply_1(v_h__1_190_, v___x_192_);
return v___x_193_;
}
else
{
lean_object* v_head_194_; lean_object* v_tail_195_; lean_object* v___x_196_; 
lean_dec(v_h__1_190_);
v_head_194_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_head_194_);
v_tail_195_ = lean_ctor_get(v_x_189_, 1);
lean_inc(v_tail_195_);
lean_dec_ref(v_x_189_);
v___x_196_ = lean_apply_2(v_h__2_191_, v_head_194_, v_tail_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_197_, lean_object* v_motive_198_, lean_object* v_x_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(v_x_199_, v_h__1_200_, v_h__2_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
if (v_x_203_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_h__1_204_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_apply_1(v_h__2_205_, v___x_206_);
return v___x_207_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_h__2_205_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_apply_1(v_h__1_204_, v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
uint8_t v_x_22__boxed_213_; lean_object* v_res_214_; 
v_x_22__boxed_213_ = lean_unbox(v_x_210_);
v_res_214_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_213_, v_h__1_211_, v_h__2_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object* v_motive_215_, uint8_t v_x_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_216_, v_h__1_217_, v_h__2_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_220_, lean_object* v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_){
_start:
{
uint8_t v_x_33__boxed_224_; lean_object* v_res_225_; 
v_x_33__boxed_224_ = lean_unbox(v_x_221_);
v_res_225_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(v_motive_220_, v_x_33__boxed_224_, v_h__1_222_, v_h__2_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_h__2_228_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_apply_1(v_h__1_227_, v___x_229_);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; 
lean_dec(v_h__1_227_);
v_val_231_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_val_231_);
lean_dec_ref(v_x_226_);
v___x_232_ = lean_apply_1(v_h__2_228_, v_val_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_233_, lean_object* v_as_234_, lean_object* v_motive_235_, lean_object* v_x_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(v_x_236_, v_h__1_237_, v_h__2_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_240_, lean_object* v_as_241_, lean_object* v_motive_242_, lean_object* v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(v_00_u03b1_240_, v_as_241_, v_motive_242_, v_x_243_, v_h__1_244_, v_h__2_245_);
lean_dec_ref(v_as_241_);
return v_res_246_;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_ToArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_ToArray(builtin);
}
#ifdef __cplusplus
}
#endif
