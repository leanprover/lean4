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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
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
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_22_; 
v_fst_3_ = lean_ctor_get(v_x_2_, 0);
v_snd_4_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_22_ == 0)
{
v___x_6_ = v_x_2_;
v_isShared_7_ = v_isSharedCheck_22_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_inc(v_fst_3_);
lean_dec(v_x_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_22_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___y_9_; uint8_t v___x_15_; uint8_t v___y_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_15_ = lean_nat_dec_lt(v_fst_3_, v_n_1_);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_dec_eq(v_fst_3_, v___x_18_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = 1;
v___y_17_ = v___x_20_;
goto v___jp_16_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = 0;
v___y_17_ = v___x_21_;
goto v___jp_16_;
}
v___jp_8_:
{
if (v___y_9_ == 0)
{
lean_object* v___x_10_; 
lean_del_object(v___x_6_);
lean_dec(v_snd_4_);
lean_dec(v_fst_3_);
v___x_10_ = lean_box(0);
return v___x_10_;
}
else
{
lean_object* v___x_12_; 
if (v_isShared_7_ == 0)
{
v___x_12_ = v___x_6_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_fst_3_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_snd_4_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
v___jp_16_:
{
if (v___x_15_ == 0)
{
v___y_9_ = v___x_15_;
goto v___jp_8_;
}
else
{
v___y_9_ = v___y_17_;
goto v___jp_8_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(lean_object* v_n_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(v_n_23_, v_x_24_);
lean_dec(v_n_23_);
return v_res_25_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_nat_to_int(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(lean_object* v_n_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; uint8_t v___y_34_; uint8_t v___y_41_; uint8_t v___x_42_; 
v___x_30_ = lean_nat_abs(v_x_29_);
v___x_31_ = lean_nat_dec_lt(v___x_30_, v_n_28_);
v___x_32_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
v___x_42_ = lean_int_dec_eq(v_x_29_, v___x_32_);
if (v___x_42_ == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 1;
v___y_41_ = v___x_43_;
goto v___jp_40_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 0;
v___y_41_ = v___x_44_;
goto v___jp_40_;
}
v___jp_33_:
{
if (v___y_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec(v___x_30_);
v___x_35_ = lean_box(0);
return v___x_35_;
}
else
{
uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_int_dec_lt(v___x_32_, v_x_29_);
v___x_37_ = lean_box(v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_30_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
v___jp_40_:
{
if (v___x_31_ == 0)
{
v___y_34_ = v___x_31_;
goto v___jp_33_;
}
else
{
v___y_34_ = v___y_41_;
goto v___jp_33_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(lean_object* v_n_45_, lean_object* v_x_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(v_n_45_, v_x_46_);
lean_dec(v_x_46_);
lean_dec(v_n_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object* v_n_48_, size_t v_sz_49_, size_t v_i_50_, lean_object* v_bs_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = lean_usize_dec_lt(v_i_50_, v_sz_49_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; 
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_bs_51_);
return v___x_53_;
}
else
{
lean_object* v_v_54_; lean_object* v___x_55_; lean_object* v_bs_x27_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; uint8_t v___y_61_; uint8_t v___y_71_; uint8_t v___x_72_; 
v_v_54_ = lean_array_uget(v_bs_51_, v_i_50_);
v___x_55_ = lean_unsigned_to_nat(0u);
v_bs_x27_56_ = lean_array_uset(v_bs_51_, v_i_50_, v___x_55_);
v___x_57_ = lean_nat_abs(v_v_54_);
v___x_58_ = lean_nat_dec_lt(v___x_57_, v_n_48_);
v___x_59_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
v___x_72_ = lean_int_dec_eq(v_v_54_, v___x_59_);
if (v___x_72_ == 0)
{
v___y_71_ = v___x_52_;
goto v___jp_70_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 0;
v___y_71_ = v___x_73_;
goto v___jp_70_;
}
v___jp_60_:
{
if (v___y_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec(v___x_57_);
lean_dec_ref(v_bs_x27_56_);
lean_dec(v_v_54_);
v___x_62_ = lean_box(0);
return v___x_62_;
}
else
{
uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; size_t v___x_66_; size_t v___x_67_; lean_object* v___x_68_; 
v___x_63_ = lean_int_dec_lt(v___x_59_, v_v_54_);
lean_dec(v_v_54_);
v___x_64_ = lean_box(v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_57_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = ((size_t)1ULL);
v___x_67_ = lean_usize_add(v_i_50_, v___x_66_);
v___x_68_ = lean_array_uset(v_bs_x27_56_, v_i_50_, v___x_65_);
v_i_50_ = v___x_67_;
v_bs_51_ = v___x_68_;
goto _start;
}
}
v___jp_70_:
{
if (v___x_58_ == 0)
{
v___y_61_ = v___x_58_;
goto v___jp_60_;
}
else
{
v___y_61_ = v___y_71_;
goto v___jp_60_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object* v_n_74_, lean_object* v_sz_75_, lean_object* v_i_76_, lean_object* v_bs_77_){
_start:
{
size_t v_sz_boxed_78_; size_t v_i_boxed_79_; lean_object* v_res_80_; 
v_sz_boxed_78_ = lean_unbox_usize(v_sz_75_);
lean_dec(v_sz_75_);
v_i_boxed_79_ = lean_unbox_usize(v_i_76_);
lean_dec(v_i_76_);
v_res_80_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_74_, v_sz_boxed_78_, v_i_boxed_79_, v_bs_77_);
lean_dec(v_n_74_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object* v_n_81_, lean_object* v_x_82_){
_start:
{
switch(lean_obj_tag(v_x_82_))
{
case 0:
{
lean_object* v_id_83_; lean_object* v_rupHints_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_id_83_ = lean_ctor_get(v_x_82_, 0);
v_rupHints_84_ = lean_ctor_get(v_x_82_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v_x_82_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_rupHints_84_);
lean_inc(v_id_83_);
lean_dec(v_x_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_id_83_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_rupHints_84_);
v___x_89_ = v_reuseFailAlloc_91_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
}
case 1:
{
lean_object* v_id_93_; lean_object* v_c_94_; lean_object* v_rupHints_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_117_; 
v_id_93_ = lean_ctor_get(v_x_82_, 0);
v_c_94_ = lean_ctor_get(v_x_82_, 1);
v_rupHints_95_ = lean_ctor_get(v_x_82_, 2);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_117_ == 0)
{
v___x_97_ = v_x_82_;
v_isShared_98_ = v_isSharedCheck_117_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_rupHints_95_);
lean_inc(v_c_94_);
lean_inc(v_id_93_);
lean_dec(v_x_82_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_117_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
size_t v_sz_99_; size_t v___x_100_; lean_object* v___x_101_; 
v_sz_99_ = lean_array_size(v_c_94_);
v___x_100_ = ((size_t)0ULL);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_81_, v_sz_99_, v___x_100_, v_c_94_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v___x_102_; 
lean_del_object(v___x_97_);
lean_dec_ref(v_rupHints_95_);
lean_dec(v_id_93_);
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_104_; 
v_val_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v___x_101_, 1);
v___x_104_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_81_, v_val_103_);
lean_dec(v_val_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v___x_105_; 
lean_del_object(v___x_97_);
lean_dec_ref(v_rupHints_95_);
lean_dec(v_id_93_);
v___x_105_ = lean_box(0);
return v___x_105_;
}
else
{
lean_object* v_val_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_116_; 
v_val_106_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_116_ == 0)
{
v___x_108_ = v___x_104_;
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_val_106_);
lean_dec(v___x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v_val_106_);
v___x_111_ = v___x_97_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_id_93_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_val_106_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_rupHints_95_);
v___x_111_ = v_reuseFailAlloc_115_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_111_);
v___x_113_ = v___x_108_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_pivot_118_; lean_object* v_id_119_; lean_object* v_c_120_; lean_object* v_rupHints_121_; lean_object* v_ratHints_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_163_; 
v_pivot_118_ = lean_ctor_get(v_x_82_, 2);
v_id_119_ = lean_ctor_get(v_x_82_, 0);
v_c_120_ = lean_ctor_get(v_x_82_, 1);
v_rupHints_121_ = lean_ctor_get(v_x_82_, 3);
v_ratHints_122_ = lean_ctor_get(v_x_82_, 4);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_163_ == 0)
{
v___x_124_ = v_x_82_;
v_isShared_125_ = v_isSharedCheck_163_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_ratHints_122_);
lean_inc(v_rupHints_121_);
lean_inc(v_pivot_118_);
lean_inc(v_c_120_);
lean_inc(v_id_119_);
lean_dec(v_x_82_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_163_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_162_; 
v_fst_126_ = lean_ctor_get(v_pivot_118_, 0);
v_snd_127_ = lean_ctor_get(v_pivot_118_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_pivot_118_);
if (v_isSharedCheck_162_ == 0)
{
v___x_129_ = v_pivot_118_;
v_isShared_130_ = v_isSharedCheck_162_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_126_);
lean_dec(v_pivot_118_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_162_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint8_t v___y_132_; uint8_t v___x_155_; uint8_t v___y_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_155_ = lean_nat_dec_lt(v_fst_126_, v_n_81_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v_fst_126_, v___x_158_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 1;
v___y_157_ = v___x_160_;
goto v___jp_156_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 0;
v___y_157_ = v___x_161_;
goto v___jp_156_;
}
v___jp_131_:
{
if (v___y_132_ == 0)
{
lean_object* v___x_133_; 
lean_del_object(v___x_129_);
lean_dec(v_snd_127_);
lean_dec(v_fst_126_);
lean_del_object(v___x_124_);
lean_dec_ref(v_ratHints_122_);
lean_dec_ref(v_rupHints_121_);
lean_dec(v_c_120_);
lean_dec(v_id_119_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
size_t v_sz_134_; size_t v___x_135_; lean_object* v___x_136_; 
v_sz_134_ = lean_array_size(v_c_120_);
v___x_135_ = ((size_t)0ULL);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_81_, v_sz_134_, v___x_135_, v_c_120_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_137_; 
lean_del_object(v___x_129_);
lean_dec(v_snd_127_);
lean_dec(v_fst_126_);
lean_del_object(v___x_124_);
lean_dec_ref(v_ratHints_122_);
lean_dec_ref(v_rupHints_121_);
lean_dec(v_id_119_);
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
lean_object* v_val_138_; lean_object* v___x_139_; 
v_val_138_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v___x_136_, 1);
v___x_139_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_81_, v_val_138_);
lean_dec(v_val_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v___x_140_; 
lean_del_object(v___x_129_);
lean_dec(v_snd_127_);
lean_dec(v_fst_126_);
lean_del_object(v___x_124_);
lean_dec_ref(v_ratHints_122_);
lean_dec_ref(v_rupHints_121_);
lean_dec(v_id_119_);
v___x_140_ = lean_box(0);
return v___x_140_;
}
else
{
lean_object* v_val_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_154_; 
v_val_141_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_154_ == 0)
{
v___x_143_ = v___x_139_;
v_isShared_144_ = v_isSharedCheck_154_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_val_141_);
lean_dec(v___x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_154_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_130_ == 0)
{
v___x_146_ = v___x_129_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_fst_126_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_snd_127_);
v___x_146_ = v_reuseFailAlloc_153_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 2, v___x_146_);
lean_ctor_set(v___x_124_, 1, v_val_141_);
v___x_148_ = v___x_124_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_id_119_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_val_141_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_rupHints_121_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_ratHints_122_);
v___x_148_ = v_reuseFailAlloc_152_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_148_);
v___x_150_ = v___x_143_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
}
}
v___jp_156_:
{
if (v___x_155_ == 0)
{
v___y_132_ = v___x_155_;
goto v___jp_131_;
}
else
{
v___y_132_ = v___y_157_;
goto v___jp_131_;
}
}
}
}
}
default: 
{
lean_object* v_ids_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
v_ids_164_ = lean_ctor_get(v_x_82_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_172_ == 0)
{
v___x_166_ = v_x_82_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_ids_164_);
lean_dec(v_x_82_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_ids_164_);
v___x_169_ = v_reuseFailAlloc_171_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction___boxed(lean_object* v_n_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(v_n_173_, v_x_174_);
lean_dec(v_n_173_);
return v_res_175_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
