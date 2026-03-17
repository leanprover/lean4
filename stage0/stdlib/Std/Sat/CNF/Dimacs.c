// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: public import Std.Sat.CNF.RelabelFin
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object*);
static const lean_string_object l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0 = (const lean_object*)&l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_CNF_dimacs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__0 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__0_value;
static const lean_string_object l_Std_Sat_CNF_dimacs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "p cnf "};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__1 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__1_value;
static const lean_string_object l_Std_Sat_CNF_dimacs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__2 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__2_value;
static const lean_string_object l_Std_Sat_CNF_dimacs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__3 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object* v_lit_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_numClauses_3_; lean_object* v_maxLit_4_; lean_object* v_fst_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_26_; 
v_numClauses_3_ = lean_ctor_get(v_a_2_, 0);
v_maxLit_4_ = lean_ctor_get(v_a_2_, 1);
v_fst_5_ = lean_ctor_get(v_lit_1_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v_lit_1_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; 
v_unused_27_ = lean_ctor_get(v_lit_1_, 1);
lean_dec(v_unused_27_);
v___x_7_ = v_lit_1_;
v_isShared_8_ = v_isSharedCheck_26_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_fst_5_);
lean_dec(v_lit_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_26_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_box(0);
v___x_10_ = lean_nat_dec_le(v_maxLit_4_, v_fst_5_);
if (v___x_10_ == 0)
{
lean_object* v___x_12_; 
lean_dec(v_fst_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_a_2_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
else
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
lean_inc(v_numClauses_3_);
v_isSharedCheck_23_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; lean_object* v_unused_25_; 
v_unused_24_ = lean_ctor_get(v_a_2_, 1);
lean_dec(v_unused_24_);
v_unused_25_ = lean_ctor_get(v_a_2_, 0);
lean_dec(v_unused_25_);
v___x_15_ = v_a_2_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v_a_2_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v_fst_5_);
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_numClauses_3_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_fst_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_18_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_20_ = v___x_7_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object* v_a_28_){
_start:
{
lean_object* v_numClauses_29_; lean_object* v_maxLit_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_41_; 
v_numClauses_29_ = lean_ctor_get(v_a_28_, 0);
v_maxLit_30_ = lean_ctor_get(v_a_28_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_a_28_);
if (v_isSharedCheck_41_ == 0)
{
v___x_32_ = v_a_28_;
v_isShared_33_ = v_isSharedCheck_41_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_maxLit_30_);
lean_inc(v_numClauses_29_);
lean_dec(v_a_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_41_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_34_ = lean_box(0);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_numClauses_29_, v___x_35_);
lean_dec(v_numClauses_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_36_);
v___x_38_ = v___x_32_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_maxLit_30_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_34_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v___y_45_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_46_; 
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_x_43_);
lean_ctor_set(v___x_46_, 1, v___y_45_);
return v___x_46_;
}
else
{
lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v___y_50_; lean_object* v___y_51_; lean_object* v_numClauses_56_; lean_object* v_maxLit_57_; lean_object* v_fst_58_; lean_object* v_snd_59_; lean_object* v_snd_61_; uint8_t v___x_71_; 
v_head_47_ = lean_ctor_get(v_x_44_, 0);
v_tail_48_ = lean_ctor_get(v_x_44_, 1);
v_numClauses_56_ = lean_ctor_get(v___y_45_, 0);
v_maxLit_57_ = lean_ctor_get(v___y_45_, 1);
v_fst_58_ = lean_ctor_get(v_head_47_, 0);
v_snd_59_ = lean_ctor_get(v_head_47_, 1);
v___x_71_ = lean_nat_dec_le(v_maxLit_57_, v_fst_58_);
if (v___x_71_ == 0)
{
v_snd_61_ = v___y_45_;
goto v___jp_60_;
}
else
{
lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_inc(v_numClauses_56_);
v_isSharedCheck_78_ = !lean_is_exclusive(v___y_45_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; lean_object* v_unused_80_; 
v_unused_79_ = lean_ctor_get(v___y_45_, 1);
lean_dec(v_unused_79_);
v_unused_80_ = lean_ctor_get(v___y_45_, 0);
lean_dec(v_unused_80_);
v___x_73_ = v___y_45_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_dec(v___y_45_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
lean_inc(v_fst_58_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v_fst_58_);
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_numClauses_56_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_fst_58_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
v_snd_61_ = v___x_76_;
goto v___jp_60_;
}
}
}
v___jp_49_:
{
lean_object* v___x_52_; uint32_t v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_string_append(v_x_43_, v___y_51_);
lean_dec_ref(v___y_51_);
v___x_53_ = 32;
v___x_54_ = lean_string_push(v___x_52_, v___x_53_);
v_x_43_ = v___x_54_;
v_x_44_ = v_tail_48_;
v___y_45_ = v___y_50_;
goto _start;
}
v___jp_60_:
{
uint8_t v___x_62_; 
v___x_62_ = lean_unbox(v_snd_59_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_63_ = ((lean_object*)(l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0));
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_fst_58_, v___x_64_);
v___x_66_ = l_Nat_reprFast(v___x_65_);
v___x_67_ = lean_string_append(v___x_63_, v___x_66_);
lean_dec_ref(v___x_66_);
v___y_50_ = v_snd_61_;
v___y_51_ = v___x_67_;
goto v___jp_49_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_fst_58_, v___x_68_);
v___x_70_ = l_Nat_reprFast(v___x_69_);
v___y_50_ = v_snd_61_;
v___y_51_ = v___x_70_;
goto v___jp_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___boxed(lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(v_x_81_, v_x_82_, v___y_83_);
lean_dec(v_x_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(lean_object* v_as_85_, size_t v_i_86_, size_t v_stop_87_, lean_object* v_b_88_, lean_object* v___y_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_usize_dec_eq(v_i_86_, v_stop_87_);
if (v___x_90_ == 0)
{
lean_object* v_numClauses_91_; lean_object* v_maxLit_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_112_; 
v_numClauses_91_ = lean_ctor_get(v___y_89_, 0);
v_maxLit_92_ = lean_ctor_get(v___y_89_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v___y_89_);
if (v_isSharedCheck_112_ == 0)
{
v___x_94_ = v___y_89_;
v_isShared_95_ = v_isSharedCheck_112_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_maxLit_92_);
lean_inc(v_numClauses_91_);
lean_dec(v___y_89_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_112_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_96_ = lean_array_uget_borrowed(v_as_85_, v_i_86_);
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_numClauses_91_, v___x_97_);
lean_dec(v_numClauses_91_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_98_);
v___x_100_ = v___x_94_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_maxLit_92_);
v___x_100_ = v_reuseFailAlloc_111_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v_fst_102_; lean_object* v_snd_103_; uint32_t v___x_104_; lean_object* v___x_105_; uint32_t v___x_106_; lean_object* v___x_107_; size_t v___x_108_; size_t v___x_109_; 
v___x_101_ = l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(v_b_88_, v___x_96_, v___x_100_);
v_fst_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_fst_102_);
v_snd_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_snd_103_);
lean_dec_ref(v___x_101_);
v___x_104_ = 48;
v___x_105_ = lean_string_push(v_fst_102_, v___x_104_);
v___x_106_ = 10;
v___x_107_ = lean_string_push(v___x_105_, v___x_106_);
v___x_108_ = ((size_t)1ULL);
v___x_109_ = lean_usize_add(v_i_86_, v___x_108_);
v_i_86_ = v___x_109_;
v_b_88_ = v___x_107_;
v___y_89_ = v_snd_103_;
goto _start;
}
}
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_b_88_);
lean_ctor_set(v___x_113_, 1, v___y_89_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v_b_117_, lean_object* v___y_118_){
_start:
{
size_t v_i_boxed_119_; size_t v_stop_boxed_120_; lean_object* v_res_121_; 
v_i_boxed_119_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_as_114_, v_i_boxed_119_, v_stop_boxed_120_, v_b_117_, v___y_118_);
lean_dec_ref(v_as_114_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(lean_object* v_cnf_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_125_ = ((lean_object*)(l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0));
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_array_get_size(v_cnf_123_);
v___x_128_ = lean_nat_dec_lt(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_125_);
lean_ctor_set(v___x_129_, 1, v_a_124_);
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_le(v___x_127_, v___x_127_);
if (v___x_130_ == 0)
{
if (v___x_128_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_125_);
lean_ctor_set(v___x_131_, 1, v_a_124_);
return v___x_131_;
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_127_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_cnf_123_, v___x_132_, v___x_133_, v___x_125_, v_a_124_);
return v___x_134_;
}
}
else
{
size_t v___x_135_; size_t v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_127_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_cnf_123_, v___x_135_, v___x_136_, v___x_125_, v_a_124_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___boxed(lean_object* v_cnf_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(v_cnf_138_, v_a_139_);
lean_dec_ref(v_cnf_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object* v_cnf_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v_snd_149_; lean_object* v_fst_150_; lean_object* v_numClauses_151_; lean_object* v_maxLit_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_147_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__0));
v___x_148_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(v_cnf_146_, v___x_147_);
v_snd_149_ = lean_ctor_get(v___x_148_, 1);
lean_inc(v_snd_149_);
v_fst_150_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_fst_150_);
lean_dec_ref(v___x_148_);
v_numClauses_151_ = lean_ctor_get(v_snd_149_, 0);
lean_inc(v_numClauses_151_);
v_maxLit_152_ = lean_ctor_get(v_snd_149_, 1);
lean_inc(v_maxLit_152_);
lean_dec(v_snd_149_);
v___x_153_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__1));
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_maxLit_152_, v___x_154_);
lean_dec(v_maxLit_152_);
v___x_156_ = l_Nat_reprFast(v___x_155_);
v___x_157_ = lean_string_append(v___x_153_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__2));
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
v___x_160_ = l_Nat_reprFast(v_numClauses_151_);
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__3));
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
v___x_164_ = lean_string_append(v___x_163_, v_fst_150_);
lean_dec(v_fst_150_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object* v_cnf_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Sat_CNF_dimacs(v_cnf_165_);
lean_dec_ref(v_cnf_165_);
return v_res_166_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Dimacs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Dimacs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Dimacs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Dimacs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Dimacs(builtin);
}
#ifdef __cplusplus
}
#endif
