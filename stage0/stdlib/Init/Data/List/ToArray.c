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
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
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
v_n_8_ = lean_nat_sub(v_x_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_x_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_14_, lean_object* v_xs_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_x_17_, v_zero_21_);
if (v_isZero_22_ == 1)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v___x_23_ = lean_apply_1(v_h__1_19_, lean_box(0));
return v___x_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_19_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_x_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, lean_box(0));
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_xs_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_27_, v_xs_28_, v_motive_29_, v_x_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_30_);
lean_dec_ref(v_xs_28_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object* v_____do__lift_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_____do__lift_35_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_37_);
v_a_38_ = lean_ctor_get(v_____do__lift_35_, 0);
lean_inc(v_a_38_);
lean_dec_ref_known(v_____do__lift_35_, 1);
v___x_39_ = lean_apply_1(v_h__1_36_, v_a_38_);
return v___x_39_;
}
else
{
lean_object* v_a_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_36_);
v_a_40_ = lean_ctor_get(v_____do__lift_35_, 0);
lean_inc(v_a_40_);
lean_dec_ref_known(v_____do__lift_35_, 1);
v___x_41_ = lean_apply_1(v_h__2_37_, v_a_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object* v_00_u03b2_42_, lean_object* v_motive_43_, lean_object* v_____do__lift_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_____do__lift_44_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_46_);
v_a_47_ = lean_ctor_get(v_____do__lift_44_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v_____do__lift_44_, 1);
v___x_48_ = lean_apply_1(v_h__1_45_, v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_45_);
v_a_49_ = lean_ctor_get(v_____do__lift_44_, 0);
lean_inc(v_a_49_);
lean_dec_ref_known(v_____do__lift_44_, 1);
v___x_50_ = lean_apply_1(v_h__2_46_, v_a_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_53_);
v_a_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v_x_51_, 1);
v___x_55_ = lean_apply_1(v_h__1_52_, v_a_54_);
return v___x_55_;
}
else
{
lean_object* v_a_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v_a_56_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_56_);
lean_dec_ref_known(v_x_51_, 1);
v___x_57_ = lean_apply_1(v_h__2_53_, v_a_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_62_);
v_a_63_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v_x_60_, 1);
v___x_64_ = lean_apply_1(v_h__1_61_, v_a_63_);
return v___x_64_;
}
else
{
lean_object* v_a_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_61_);
v_a_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v_x_60_, 1);
v___x_66_ = lean_apply_1(v_h__2_62_, v_a_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_____do__lift_67_) == 1)
{
lean_object* v_val_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_69_);
v_val_70_ = lean_ctor_get(v_____do__lift_67_, 0);
lean_inc(v_val_70_);
lean_dec_ref_known(v_____do__lift_67_, 1);
v___x_71_ = lean_apply_1(v_h__1_68_, v_val_70_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; 
lean_dec(v_h__1_68_);
v___x_72_ = lean_apply_2(v_h__2_69_, v_____do__lift_67_, lean_box(0));
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_73_, lean_object* v_motive_74_, lean_object* v_____do__lift_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_____do__lift_75_) == 1)
{
lean_object* v_val_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_77_);
v_val_78_ = lean_ctor_get(v_____do__lift_75_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_____do__lift_75_, 1);
v___x_79_ = lean_apply_1(v_h__1_76_, v_val_78_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
lean_dec(v_h__1_76_);
v___x_80_ = lean_apply_2(v_h__2_77_, v_____do__lift_75_, lean_box(0));
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__2_83_, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_83_);
v_val_86_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v_x_81_, 1);
v___x_87_ = lean_apply_1(v_h__1_82_, v_val_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_88_, lean_object* v_motive_89_, lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_91_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_1(v_h__2_92_, v___x_93_);
return v___x_94_;
}
else
{
lean_object* v_val_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_92_);
v_val_95_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v_x_90_, 1);
v___x_96_ = lean_apply_1(v_h__1_91_, v_val_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_99_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__1_98_, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_98_);
v_head_102_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_x_97_, 1);
lean_inc(v_tail_103_);
lean_dec_ref_known(v_x_97_, 2);
v___x_104_ = lean_apply_2(v_h__2_99_, v_head_102_, v_tail_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_109_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_1(v_h__1_108_, v___x_110_);
return v___x_111_;
}
else
{
lean_object* v_head_112_; lean_object* v_tail_113_; lean_object* v___x_114_; 
lean_dec(v_h__1_108_);
v_head_112_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_head_112_);
v_tail_113_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_tail_113_);
lean_dec_ref_known(v_x_107_, 2);
v___x_114_ = lean_apply_2(v_h__2_109_, v_head_112_, v_tail_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (lean_obj_tag(v_____do__lift_115_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_h__1_116_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_1(v_h__2_117_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_117_);
v_val_120_ = lean_ctor_get(v_____do__lift_115_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_____do__lift_115_, 1);
v___x_121_ = lean_apply_1(v_h__1_116_, v_val_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_122_, lean_object* v_motive_123_, lean_object* v_____do__lift_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
if (lean_obj_tag(v_____do__lift_124_) == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_h__1_125_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_apply_1(v_h__2_126_, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_126_);
v_val_129_ = lean_ctor_get(v_____do__lift_124_, 0);
lean_inc(v_val_129_);
lean_dec_ref_known(v_____do__lift_124_, 1);
v___x_130_ = lean_apply_1(v_h__1_125_, v_val_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* v_r_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
if (lean_obj_tag(v_r_131_) == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_h__1_132_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_apply_1(v_h__2_133_, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v_val_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_133_);
v_val_136_ = lean_ctor_get(v_r_131_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v_r_131_, 1);
v___x_137_ = lean_apply_1(v_h__1_132_, v_val_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* v_00_u03b2_138_, lean_object* v_motive_139_, lean_object* v_r_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
if (lean_obj_tag(v_r_140_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_h__1_141_);
v___x_143_ = lean_box(0);
v___x_144_ = lean_apply_1(v_h__2_142_, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v_val_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_142_);
v_val_145_ = lean_ctor_get(v_r_140_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v_r_140_, 1);
v___x_146_ = lean_apply_1(v_h__1_141_, v_val_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_h__2_149_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_apply_1(v_h__1_148_, v___x_150_);
return v___x_151_;
}
else
{
lean_object* v_head_152_; lean_object* v_tail_153_; lean_object* v___x_154_; 
lean_dec(v_h__1_148_);
v_head_152_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_head_152_);
v_tail_153_ = lean_ctor_get(v_x_147_, 1);
lean_inc(v_tail_153_);
lean_dec_ref_known(v_x_147_, 2);
v___x_154_ = lean_apply_2(v_h__2_149_, v_head_152_, v_tail_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(lean_object* v_00_u03b1_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__2_159_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__1_158_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_head_162_; lean_object* v_tail_163_; lean_object* v___x_164_; 
lean_dec(v_h__1_158_);
v_head_162_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_head_162_);
v_tail_163_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_tail_163_);
lean_dec_ref_known(v_x_157_, 2);
v___x_164_ = lean_apply_2(v_h__2_159_, v_head_162_, v_tail_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
if (v_____do__lift_165_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__1_166_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_1(v_h__2_167_, v___x_168_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_h__2_167_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_1(v_h__1_166_, v___x_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_){
_start:
{
uint8_t v_____do__lift_24__boxed_175_; lean_object* v_res_176_; 
v_____do__lift_24__boxed_175_ = lean_unbox(v_____do__lift_172_);
v_res_176_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_175_, v_h__1_173_, v_h__2_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object* v_motive_177_, uint8_t v_____do__lift_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
if (v_____do__lift_178_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_179_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_1(v_h__2_180_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_180_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__1_179_, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_185_, lean_object* v_____do__lift_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
uint8_t v_____do__lift_35__boxed_189_; lean_object* v_res_190_; 
v_____do__lift_35__boxed_189_ = lean_unbox(v_____do__lift_186_);
v_res_190_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(v_motive_185_, v_____do__lift_35__boxed_189_, v_h__1_187_, v_h__2_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_h__2_193_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_apply_1(v_h__1_192_, v___x_194_);
return v___x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_192_);
v_head_196_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_head_196_);
v_tail_197_ = lean_ctor_get(v_x_191_, 1);
lean_inc(v_tail_197_);
lean_dec_ref_known(v_x_191_, 2);
v___x_198_ = lean_apply_2(v_h__2_193_, v_head_196_, v_tail_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_199_, lean_object* v_motive_200_, lean_object* v_x_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_h__2_203_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_1(v_h__1_202_, v___x_204_);
return v___x_205_;
}
else
{
lean_object* v_head_206_; lean_object* v_tail_207_; lean_object* v___x_208_; 
lean_dec(v_h__1_202_);
v_head_206_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_head_206_);
v_tail_207_ = lean_ctor_get(v_x_201_, 1);
lean_inc(v_tail_207_);
lean_dec_ref_known(v_x_201_, 2);
v___x_208_ = lean_apply_2(v_h__2_203_, v_head_206_, v_tail_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t v_x_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_){
_start:
{
if (v_x_209_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_h__1_210_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_1(v_h__2_211_, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_h__2_211_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_1(v_h__1_210_, v___x_214_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
uint8_t v_x_24__boxed_219_; lean_object* v_res_220_; 
v_x_24__boxed_219_ = lean_unbox(v_x_216_);
v_res_220_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_219_, v_h__1_217_, v_h__2_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object* v_motive_221_, uint8_t v_x_222_, lean_object* v_h__1_223_, lean_object* v_h__2_224_){
_start:
{
if (v_x_222_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_223_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_apply_1(v_h__2_224_, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_h__2_224_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_apply_1(v_h__1_223_, v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_229_, lean_object* v_x_230_, lean_object* v_h__1_231_, lean_object* v_h__2_232_){
_start:
{
uint8_t v_x_35__boxed_233_; lean_object* v_res_234_; 
v_x_35__boxed_233_ = lean_unbox(v_x_230_);
v_res_234_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(v_motive_229_, v_x_35__boxed_233_, v_h__1_231_, v_h__2_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_h__2_237_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_apply_1(v_h__1_236_, v___x_238_);
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; 
lean_dec(v_h__1_236_);
v_val_240_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v_x_235_, 1);
v___x_241_ = lean_apply_1(v_h__2_237_, v_val_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_242_, lean_object* v_as_243_, lean_object* v_motive_244_, lean_object* v_x_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_247_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_apply_1(v_h__1_246_, v___x_248_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; lean_object* v___x_251_; 
lean_dec(v_h__1_246_);
v_val_250_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v_x_245_, 1);
v___x_251_ = lean_apply_1(v_h__2_247_, v_val_250_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_252_, lean_object* v_as_253_, lean_object* v_motive_254_, lean_object* v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(v_00_u03b1_252_, v_as_253_, v_motive_254_, v_x_255_, v_h__1_256_, v_h__2_257_);
lean_dec_ref(v_as_253_);
return v_res_258_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
