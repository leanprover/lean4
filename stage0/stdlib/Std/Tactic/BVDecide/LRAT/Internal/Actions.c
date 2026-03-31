// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Actions
// Imports: public import Std.Tactic.BVDecide.LRAT.Actions public import Std.Tactic.BVDecide.LRAT.Internal.Clause
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(lean_object* v_n_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_18_; 
v_fst_3_ = lean_ctor_get(v_x_2_, 0);
v_snd_4_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_6_ = v_x_2_;
v_isShared_7_ = v_isSharedCheck_18_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_inc(v_fst_3_);
lean_dec(v_x_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_18_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_lt(v_fst_3_, v_n_1_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_del_object(v___x_6_);
lean_dec(v_snd_4_);
lean_dec(v_fst_3_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_nat_dec_eq(v_fst_3_, v___x_10_);
if (v___x_11_ == 0)
{
if (v___x_8_ == 0)
{
lean_object* v___x_12_; 
lean_del_object(v___x_6_);
lean_dec(v_snd_4_);
lean_dec(v_fst_3_);
v___x_12_ = lean_box(0);
return v___x_12_;
}
else
{
lean_object* v___x_14_; 
if (v_isShared_7_ == 0)
{
v___x_14_ = v___x_6_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_fst_3_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_snd_4_);
v___x_14_ = v_reuseFailAlloc_16_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
}
else
{
lean_object* v___x_17_; 
lean_del_object(v___x_6_);
lean_dec(v_snd_4_);
lean_dec(v_fst_3_);
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(lean_object* v_n_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(v_n_19_, v_x_20_);
lean_dec(v_n_19_);
return v_res_21_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_to_int(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(lean_object* v_n_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_nat_abs(v_x_25_);
v___x_27_ = lean_nat_dec_lt(v___x_26_, v_n_24_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_dec(v___x_26_);
v___x_28_ = lean_box(0);
return v___x_28_;
}
else
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
v___x_30_ = lean_int_dec_eq(v_x_25_, v___x_29_);
if (v___x_30_ == 0)
{
if (v___x_27_ == 0)
{
lean_object* v___x_31_; 
lean_dec(v___x_26_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
else
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = lean_int_dec_lt(v___x_29_, v_x_25_);
v___x_33_ = lean_box(v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_26_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
else
{
lean_object* v___x_36_; 
lean_dec(v___x_26_);
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(lean_object* v_n_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(v_n_37_, v_x_38_);
lean_dec(v_x_38_);
lean_dec(v_n_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object* v_n_40_, size_t v_sz_41_, size_t v_i_42_, lean_object* v_bs_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = lean_usize_dec_lt(v_i_42_, v_sz_41_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v_bs_43_);
return v___x_45_;
}
else
{
lean_object* v_v_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_v_46_ = lean_array_uget(v_bs_43_, v_i_42_);
v___x_47_ = lean_nat_abs(v_v_46_);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v_n_40_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec(v___x_47_);
lean_dec(v_v_46_);
lean_dec_ref(v_bs_43_);
v___x_49_ = lean_box(0);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
v___x_52_ = lean_int_dec_eq(v_v_46_, v___x_51_);
if (v___x_52_ == 0)
{
if (v___x_48_ == 0)
{
lean_object* v___x_53_; 
lean_dec(v___x_47_);
lean_dec(v_v_46_);
lean_dec_ref(v_bs_43_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v_bs_x27_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v_bs_x27_54_ = lean_array_uset(v_bs_43_, v_i_42_, v___x_50_);
v___x_55_ = lean_int_dec_lt(v___x_51_, v_v_46_);
lean_dec(v_v_46_);
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_47_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_42_, v___x_58_);
v___x_60_ = lean_array_uset(v_bs_x27_54_, v_i_42_, v___x_57_);
v_i_42_ = v___x_59_;
v_bs_43_ = v___x_60_;
goto _start;
}
}
else
{
lean_object* v___x_62_; 
lean_dec(v___x_47_);
lean_dec(v_v_46_);
lean_dec_ref(v_bs_43_);
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object* v_n_63_, lean_object* v_sz_64_, lean_object* v_i_65_, lean_object* v_bs_66_){
_start:
{
size_t v_sz_boxed_67_; size_t v_i_boxed_68_; lean_object* v_res_69_; 
v_sz_boxed_67_ = lean_unbox_usize(v_sz_64_);
lean_dec(v_sz_64_);
v_i_boxed_68_ = lean_unbox_usize(v_i_65_);
lean_dec(v_i_65_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_63_, v_sz_boxed_67_, v_i_boxed_68_, v_bs_66_);
lean_dec(v_n_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object* v_n_70_, lean_object* v_x_71_){
_start:
{
switch(lean_obj_tag(v_x_71_))
{
case 0:
{
lean_object* v_id_72_; lean_object* v_rupHints_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
v_id_72_ = lean_ctor_get(v_x_71_, 0);
v_rupHints_73_ = lean_ctor_get(v_x_71_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v_x_71_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_rupHints_73_);
lean_inc(v_id_72_);
lean_dec(v_x_71_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_id_72_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_rupHints_73_);
v___x_78_ = v_reuseFailAlloc_80_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
}
case 1:
{
lean_object* v_id_82_; lean_object* v_c_83_; lean_object* v_rupHints_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_106_; 
v_id_82_ = lean_ctor_get(v_x_71_, 0);
v_c_83_ = lean_ctor_get(v_x_71_, 1);
v_rupHints_84_ = lean_ctor_get(v_x_71_, 2);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_106_ == 0)
{
v___x_86_ = v_x_71_;
v_isShared_87_ = v_isSharedCheck_106_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_rupHints_84_);
lean_inc(v_c_83_);
lean_inc(v_id_82_);
lean_dec(v_x_71_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_106_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
size_t v_sz_88_; size_t v___x_89_; lean_object* v___x_90_; 
v_sz_88_ = lean_array_size(v_c_83_);
v___x_89_ = ((size_t)0ULL);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_70_, v_sz_88_, v___x_89_, v_c_83_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_del_object(v___x_86_);
lean_dec_ref(v_rupHints_84_);
lean_dec(v_id_82_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_93_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_val_92_);
lean_dec_ref(v___x_90_);
v___x_93_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_70_, v_val_92_);
lean_dec(v_val_92_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v___x_94_; 
lean_del_object(v___x_86_);
lean_dec_ref(v_rupHints_84_);
lean_dec(v_id_82_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v_val_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_105_; 
v_val_95_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_105_ == 0)
{
v___x_97_ = v___x_93_;
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_val_95_);
lean_dec(v___x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_val_95_);
v___x_100_ = v___x_86_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_id_82_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_val_95_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v_rupHints_84_);
v___x_100_ = v_reuseFailAlloc_104_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_pivot_107_; lean_object* v_id_108_; lean_object* v_c_109_; lean_object* v_rupHints_110_; lean_object* v_ratHints_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_148_; 
v_pivot_107_ = lean_ctor_get(v_x_71_, 2);
v_id_108_ = lean_ctor_get(v_x_71_, 0);
v_c_109_ = lean_ctor_get(v_x_71_, 1);
v_rupHints_110_ = lean_ctor_get(v_x_71_, 3);
v_ratHints_111_ = lean_ctor_get(v_x_71_, 4);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_148_ == 0)
{
v___x_113_ = v_x_71_;
v_isShared_114_ = v_isSharedCheck_148_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_ratHints_111_);
lean_inc(v_rupHints_110_);
lean_inc(v_pivot_107_);
lean_inc(v_c_109_);
lean_inc(v_id_108_);
lean_dec(v_x_71_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_148_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_147_; 
v_fst_115_ = lean_ctor_get(v_pivot_107_, 0);
v_snd_116_ = lean_ctor_get(v_pivot_107_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_pivot_107_);
if (v_isSharedCheck_147_ == 0)
{
v___x_118_ = v_pivot_107_;
v_isShared_119_ = v_isSharedCheck_147_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_pivot_107_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_147_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_lt(v_fst_115_, v_n_70_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
lean_dec_ref(v_ratHints_111_);
lean_dec_ref(v_rupHints_110_);
lean_dec(v_c_109_);
lean_dec(v_id_108_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_eq(v_fst_115_, v___x_122_);
if (v___x_123_ == 0)
{
if (v___x_120_ == 0)
{
lean_object* v___x_124_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
lean_dec_ref(v_ratHints_111_);
lean_dec_ref(v_rupHints_110_);
lean_dec(v_c_109_);
lean_dec(v_id_108_);
v___x_124_ = lean_box(0);
return v___x_124_;
}
else
{
size_t v_sz_125_; size_t v___x_126_; lean_object* v___x_127_; 
v_sz_125_ = lean_array_size(v_c_109_);
v___x_126_ = ((size_t)0ULL);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_70_, v_sz_125_, v___x_126_, v_c_109_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_128_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
lean_dec_ref(v_ratHints_111_);
lean_dec_ref(v_rupHints_110_);
lean_dec(v_id_108_);
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; 
v_val_129_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_val_129_);
lean_dec_ref(v___x_127_);
v___x_130_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_70_, v_val_129_);
lean_dec(v_val_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v___x_131_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
lean_dec_ref(v_ratHints_111_);
lean_dec_ref(v_rupHints_110_);
lean_dec(v_id_108_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v_val_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_145_; 
v_val_132_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_145_ == 0)
{
v___x_134_ = v___x_130_;
v_isShared_135_ = v_isSharedCheck_145_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_val_132_);
lean_dec(v___x_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_145_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_119_ == 0)
{
v___x_137_ = v___x_118_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_snd_116_);
v___x_137_ = v_reuseFailAlloc_144_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 2, v___x_137_);
lean_ctor_set(v___x_113_, 1, v_val_132_);
v___x_139_ = v___x_113_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_id_108_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_val_132_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_rupHints_110_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_ratHints_111_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_139_);
v___x_141_ = v___x_134_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_146_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
lean_dec_ref(v_ratHints_111_);
lean_dec_ref(v_rupHints_110_);
lean_dec(v_c_109_);
lean_dec(v_id_108_);
v___x_146_ = lean_box(0);
return v___x_146_;
}
}
}
}
}
default: 
{
lean_object* v_ids_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_ids_149_ = lean_ctor_get(v_x_71_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_x_71_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_ids_149_);
lean_dec(v_x_71_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_ids_149_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction___boxed(lean_object* v_n_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(v_n_158_, v_x_159_);
lean_dec(v_n_158_);
return v_res_160_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
}
#ifdef __cplusplus
}
#endif
