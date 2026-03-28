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
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_i_17_, v_zero_21_);
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
v_n_25_ = lean_nat_sub(v_i_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, lean_box(0));
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_27_, lean_object* v_as_28_, lean_object* v_motive_29_, lean_object* v_i_30_, lean_object* v_h_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(v_00_u03b1_27_, v_as_28_, v_motive_29_, v_i_30_, v_h_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_i_30_);
lean_dec_ref(v_as_28_);
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
lean_dec_ref(v_____do__lift_35_);
v___x_39_ = lean_apply_1(v_h__1_36_, v_a_38_);
return v___x_39_;
}
else
{
lean_object* v_a_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_36_);
v_a_40_ = lean_ctor_get(v_____do__lift_35_, 0);
lean_inc(v_a_40_);
lean_dec_ref(v_____do__lift_35_);
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
lean_dec_ref(v_____do__lift_44_);
v___x_48_ = lean_apply_1(v_h__1_45_, v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_45_);
v_a_49_ = lean_ctor_get(v_____do__lift_44_, 0);
lean_inc(v_a_49_);
lean_dec_ref(v_____do__lift_44_);
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
lean_dec_ref(v_x_51_);
v___x_55_ = lean_apply_1(v_h__1_52_, v_a_54_);
return v___x_55_;
}
else
{
lean_object* v_a_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v_a_56_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_a_56_);
lean_dec_ref(v_x_51_);
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
lean_dec_ref(v_x_60_);
v___x_64_ = lean_apply_1(v_h__1_61_, v_a_63_);
return v___x_64_;
}
else
{
lean_object* v_a_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_61_);
v_a_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_65_);
lean_dec_ref(v_x_60_);
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
lean_dec_ref(v_____do__lift_67_);
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
lean_dec_ref(v_____do__lift_75_);
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
lean_dec_ref(v_x_81_);
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
lean_dec_ref(v_x_90_);
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
lean_dec_ref(v_x_97_);
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
lean_dec_ref(v_x_107_);
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
lean_dec_ref(v_____do__lift_115_);
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
lean_dec_ref(v_____do__lift_124_);
v___x_130_ = lean_apply_1(v_h__1_125_, v_val_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
lean_object* v_zero_134_; uint8_t v_isZero_135_; 
v_zero_134_ = lean_unsigned_to_nat(0u);
v_isZero_135_ = lean_nat_dec_eq(v_x_131_, v_zero_134_);
if (v_isZero_135_ == 1)
{
lean_object* v___x_136_; 
lean_dec(v_h__2_133_);
v___x_136_ = lean_apply_1(v_h__1_132_, lean_box(0));
return v___x_136_;
}
else
{
lean_object* v_one_137_; lean_object* v_n_138_; lean_object* v___x_139_; 
lean_dec(v_h__1_132_);
v_one_137_ = lean_unsigned_to_nat(1u);
v_n_138_ = lean_nat_sub(v_x_131_, v_one_137_);
v___x_139_ = lean_apply_2(v_h__2_133_, v_n_138_, lean_box(0));
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(v_x_140_, v_h__1_141_, v_h__2_142_);
lean_dec(v_x_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object* v_00_u03b1_144_, lean_object* v_xs_145_, lean_object* v_motive_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_h__1_149_, lean_object* v_h__2_150_){
_start:
{
lean_object* v_zero_151_; uint8_t v_isZero_152_; 
v_zero_151_ = lean_unsigned_to_nat(0u);
v_isZero_152_ = lean_nat_dec_eq(v_x_147_, v_zero_151_);
if (v_isZero_152_ == 1)
{
lean_object* v___x_153_; 
lean_dec(v_h__2_150_);
v___x_153_ = lean_apply_1(v_h__1_149_, lean_box(0));
return v___x_153_;
}
else
{
lean_object* v_one_154_; lean_object* v_n_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_149_);
v_one_154_ = lean_unsigned_to_nat(1u);
v_n_155_ = lean_nat_sub(v_x_147_, v_one_154_);
v___x_156_ = lean_apply_2(v_h__2_150_, v_n_155_, lean_box(0));
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* v_00_u03b1_157_, lean_object* v_xs_158_, lean_object* v_motive_159_, lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(v_00_u03b1_157_, v_xs_158_, v_motive_159_, v_x_160_, v_x_161_, v_h__1_162_, v_h__2_163_);
lean_dec(v_x_160_);
lean_dec_ref(v_xs_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* v_r_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_){
_start:
{
if (lean_obj_tag(v_r_165_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__1_166_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_1(v_h__2_167_, v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_171_; 
lean_dec(v_h__2_167_);
v_val_170_ = lean_ctor_get(v_r_165_, 0);
lean_inc(v_val_170_);
lean_dec_ref(v_r_165_);
v___x_171_ = lean_apply_1(v_h__1_166_, v_val_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* v_00_u03b2_172_, lean_object* v_motive_173_, lean_object* v_r_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (lean_obj_tag(v_r_174_) == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__1_175_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__2_176_, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v_val_179_; lean_object* v___x_180_; 
lean_dec(v_h__2_176_);
v_val_179_ = lean_ctor_get(v_r_174_, 0);
lean_inc(v_val_179_);
lean_dec_ref(v_r_174_);
v___x_180_ = lean_apply_1(v_h__1_175_, v_val_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(lean_object* v_x_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__2_183_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_apply_1(v_h__1_182_, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v_tail_187_; lean_object* v___x_188_; 
lean_dec(v_h__1_182_);
v_head_186_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_head_186_);
v_tail_187_ = lean_ctor_get(v_x_181_, 1);
lean_inc(v_tail_187_);
lean_dec_ref(v_x_181_);
v___x_188_ = lean_apply_2(v_h__2_183_, v_head_186_, v_tail_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(lean_object* v_00_u03b1_189_, lean_object* v_motive_190_, lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
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
lean_dec_ref(v_x_191_);
v___x_198_ = lean_apply_2(v_h__2_193_, v_head_196_, v_tail_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
if (v_____do__lift_199_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_h__1_200_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_1(v_h__2_201_, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_h__2_201_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_1(v_h__1_200_, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_206_, lean_object* v_h__1_207_, lean_object* v_h__2_208_){
_start:
{
uint8_t v_____do__lift_26__boxed_209_; lean_object* v_res_210_; 
v_____do__lift_26__boxed_209_ = lean_unbox(v_____do__lift_206_);
v_res_210_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(v_____do__lift_26__boxed_209_, v_h__1_207_, v_h__2_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object* v_motive_211_, uint8_t v_____do__lift_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
if (v_____do__lift_212_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_h__1_213_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_apply_1(v_h__2_214_, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v_h__2_214_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_apply_1(v_h__1_213_, v___x_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_219_, lean_object* v_____do__lift_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
uint8_t v_____do__lift_37__boxed_223_; lean_object* v_res_224_; 
v_____do__lift_37__boxed_223_ = lean_unbox(v_____do__lift_220_);
v_res_224_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(v_motive_219_, v_____do__lift_37__boxed_223_, v_h__1_221_, v_h__2_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_h__2_227_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v_h__1_226_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_head_230_; lean_object* v_tail_231_; lean_object* v___x_232_; 
lean_dec(v_h__1_226_);
v_head_230_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_head_230_);
v_tail_231_ = lean_ctor_get(v_x_225_, 1);
lean_inc(v_tail_231_);
lean_dec_ref(v_x_225_);
v___x_232_ = lean_apply_2(v_h__2_227_, v_head_230_, v_tail_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_233_, lean_object* v_motive_234_, lean_object* v_x_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
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
lean_object* v_head_240_; lean_object* v_tail_241_; lean_object* v___x_242_; 
lean_dec(v_h__1_236_);
v_head_240_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_head_240_);
v_tail_241_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_tail_241_);
lean_dec_ref(v_x_235_);
v___x_242_ = lean_apply_2(v_h__2_237_, v_head_240_, v_tail_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (v_x_243_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__1_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__2_245_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_245_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_apply_1(v_h__1_244_, v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
uint8_t v_x_26__boxed_253_; lean_object* v_res_254_; 
v_x_26__boxed_253_ = lean_unbox(v_x_250_);
v_res_254_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_253_, v_h__1_251_, v_h__2_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object* v_motive_255_, uint8_t v_x_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
if (v_x_256_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_h__1_257_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_apply_1(v_h__2_258_, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_h__2_258_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_apply_1(v_h__1_257_, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_263_, lean_object* v_x_264_, lean_object* v_h__1_265_, lean_object* v_h__2_266_){
_start:
{
uint8_t v_x_37__boxed_267_; lean_object* v_res_268_; 
v_x_37__boxed_267_ = lean_unbox(v_x_264_);
v_res_268_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(v_motive_263_, v_x_37__boxed_267_, v_h__1_265_, v_h__2_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object* v_x_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_h__2_271_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_apply_1(v_h__1_270_, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_275_; 
lean_dec(v_h__1_270_);
v_val_274_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_val_274_);
lean_dec_ref(v_x_269_);
v___x_275_ = lean_apply_1(v_h__2_271_, v_val_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object* v_00_u03b1_276_, lean_object* v_as_277_, lean_object* v_motive_278_, lean_object* v_x_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_h__2_281_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_apply_1(v_h__1_280_, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_285_; 
lean_dec(v_h__1_280_);
v_val_284_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_val_284_);
lean_dec_ref(v_x_279_);
v___x_285_ = lean_apply_1(v_h__2_281_, v_val_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object* v_00_u03b1_286_, lean_object* v_as_287_, lean_object* v_motive_288_, lean_object* v_x_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(v_00_u03b1_286_, v_as_287_, v_motive_288_, v_x_289_, v_h__1_290_, v_h__2_291_);
lean_dec_ref(v_as_287_);
return v_res_292_;
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
