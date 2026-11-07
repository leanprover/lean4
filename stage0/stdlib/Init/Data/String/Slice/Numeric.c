// Lean compiler output
// Module: Init.Data.String.Slice.Numeric
// Imports: public import Init.Data.String.Basic import Init.Data.String.Iterate import Init.Data.String.Slice.Pattern
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_isNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_isNat___closed__0 = (const lean_object*)&l_String_Slice_isNat___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object*);
static const lean_string_object l_String_Slice_toNat_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Init.Data.String.Slice.Numeric"};
static const lean_object* l_String_Slice_toNat_x21___closed__0 = (const lean_object*)&l_String_Slice_toNat_x21___closed__0_value;
static const lean_string_object l_String_Slice_toNat_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "String.Slice.toNat!"};
static const lean_object* l_String_Slice_toNat_x21___closed__1 = (const lean_object*)&l_String_Slice_toNat_x21___closed__1_value;
static const lean_string_object l_String_Slice_toNat_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Nat expected"};
static const lean_object* l_String_Slice_toNat_x21___closed__2 = (const lean_object*)&l_String_Slice_toNat_x21___closed__2_value;
static lean_once_cell_t l_String_Slice_toNat_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_toNat_x21___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object*);
static const lean_string_object l_String_Slice_toInt_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Int expected"};
static const lean_object* l_String_Slice_toInt_x21___closed__0 = (const lean_object*)&l_String_Slice_toInt_x21___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object* v_s_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v_str_4_; lean_object* v_startInclusive_5_; lean_object* v_endExclusive_6_; lean_object* v___x_7_; uint8_t v_decide_8_; 
v_str_4_ = lean_ctor_get(v_s_1_, 0);
v_startInclusive_5_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_6_ = lean_ctor_get(v_s_1_, 2);
v___x_7_ = lean_nat_sub(v_endExclusive_6_, v_startInclusive_5_);
v_decide_8_ = lean_nat_dec_eq(v_a_2_, v___x_7_);
lean_dec(v___x_7_);
if (v_decide_8_ == 0)
{
lean_object* v_snd_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_40_; 
v_snd_9_ = lean_ctor_get(v_b_3_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_b_3_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v_b_3_, 0);
lean_dec(v_unused_41_);
v___x_11_ = v_b_3_;
v_isShared_12_ = v_isSharedCheck_40_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_snd_9_);
lean_dec(v_b_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_40_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint32_t v___x_23_; uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_19_ = lean_box(0);
v___x_20_ = lean_nat_add(v_startInclusive_5_, v_a_2_);
lean_dec(v_a_2_);
v___x_21_ = lean_string_utf8_next_fast(v_str_4_, v___x_20_);
v___x_22_ = lean_nat_sub(v___x_21_, v_startInclusive_5_);
v___x_23_ = lean_string_utf8_get_fast(v_str_4_, v___x_20_);
lean_dec(v___x_20_);
v___x_24_ = 95;
v___x_25_ = lean_uint32_dec_eq(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 48;
v___x_27_ = lean_uint32_dec_le(v___x_26_, v___x_23_);
if (v___x_27_ == 0)
{
lean_dec(v___x_22_);
goto v___jp_13_;
}
else
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 57;
v___x_29_ = lean_uint32_dec_le(v___x_23_, v___x_28_);
if (v___x_29_ == 0)
{
lean_dec(v___x_22_);
goto v___jp_13_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_del_object(v___x_11_);
lean_dec(v_snd_9_);
v___x_30_ = lean_box(v___x_27_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_19_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
v_a_2_ = v___x_22_;
v_b_3_ = v___x_31_;
goto _start;
}
}
}
else
{
uint8_t v___x_33_; 
lean_del_object(v___x_11_);
v___x_33_ = lean_unbox(v_snd_9_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v___x_22_);
v___x_34_ = lean_box(v_decide_8_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v_snd_9_);
return v___x_36_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec(v_snd_9_);
v___x_37_ = lean_box(v_decide_8_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_19_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v_a_2_ = v___x_22_;
v_b_3_ = v___x_38_;
goto _start;
}
}
v___jp_13_:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_14_ = lean_box(v_decide_8_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 0, v___x_15_);
v___x_17_ = v___x_11_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_snd_9_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
else
{
lean_dec(v_a_2_);
return v_b_3_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object* v_s_42_, lean_object* v_a_43_, lean_object* v_b_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_42_, v_a_43_, v_b_44_);
lean_dec_ref(v_s_42_);
return v_res_45_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_fst_54_; 
v___x_51_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_50_, v___x_52_, v___x_51_);
v_fst_54_ = lean_ctor_get(v___x_53_, 0);
if (lean_obj_tag(v_fst_54_) == 0)
{
lean_object* v_snd_55_; uint8_t v___x_56_; 
v_snd_55_ = lean_ctor_get(v___x_53_, 1);
lean_inc(v_snd_55_);
lean_dec_ref(v___x_53_);
v___x_56_ = lean_unbox(v_snd_55_);
lean_dec(v_snd_55_);
return v___x_56_;
}
else
{
lean_object* v_val_57_; uint8_t v___x_58_; 
lean_inc_ref(v_fst_54_);
lean_dec_ref(v___x_53_);
v_val_57_ = lean_ctor_get(v_fst_54_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_fst_54_, 1);
v___x_58_ = lean_unbox(v_val_57_);
lean_dec(v_val_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_String_Slice_isNat(v_s_59_);
lean_dec_ref(v_s_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object* v_s_62_, lean_object* v_inst_63_, lean_object* v_R_64_, lean_object* v_a_65_, lean_object* v_b_66_, lean_object* v_c_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_62_, v_a_65_, v_b_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object* v_s_69_, lean_object* v_inst_70_, lean_object* v_R_71_, lean_object* v_a_72_, lean_object* v_b_73_, lean_object* v_c_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(v_s_69_, v_inst_70_, v_R_71_, v_a_72_, v_b_73_, v_c_74_);
lean_dec_ref(v_s_69_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
lean_object* v_str_79_; lean_object* v_startInclusive_80_; lean_object* v_endExclusive_81_; lean_object* v___x_82_; uint8_t v_decide_83_; 
v_str_79_ = lean_ctor_get(v_s_76_, 0);
v_startInclusive_80_ = lean_ctor_get(v_s_76_, 1);
v_endExclusive_81_ = lean_ctor_get(v_s_76_, 2);
v___x_82_ = lean_nat_sub(v_endExclusive_81_, v_startInclusive_80_);
v_decide_83_ = lean_nat_dec_eq(v_a_77_, v___x_82_);
lean_dec(v___x_82_);
if (v_decide_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint32_t v___x_87_; uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_84_ = lean_nat_add(v_startInclusive_80_, v_a_77_);
lean_dec(v_a_77_);
v___x_85_ = lean_string_utf8_next_fast(v_str_79_, v___x_84_);
v___x_86_ = lean_nat_sub(v___x_85_, v_startInclusive_80_);
v___x_87_ = lean_string_utf8_get_fast(v_str_79_, v___x_84_);
lean_dec(v___x_84_);
v___x_88_ = 95;
v___x_89_ = lean_uint32_dec_eq(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_90_ = lean_unsigned_to_nat(10u);
v___x_91_ = lean_nat_mul(v_b_78_, v___x_90_);
lean_dec(v_b_78_);
v___x_92_ = lean_uint32_to_nat(v___x_87_);
v___x_93_ = lean_unsigned_to_nat(48u);
v___x_94_ = lean_nat_sub(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_nat_add(v___x_91_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_91_);
v_a_77_ = v___x_86_;
v_b_78_ = v___x_95_;
goto _start;
}
else
{
v_a_77_ = v___x_86_;
goto _start;
}
}
else
{
lean_dec(v_a_77_);
return v_b_78_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_98_, lean_object* v_a_99_, lean_object* v_b_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_98_, v_a_99_, v_b_100_);
lean_dec_ref(v_s_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_String_Slice_isNat(v_s_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_102_, v___x_105_, v___x_105_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_String_Slice_toNat_x3f(v_s_108_);
lean_dec_ref(v_s_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_110_, lean_object* v_inst_111_, lean_object* v_R_112_, lean_object* v_a_113_, lean_object* v_b_114_, lean_object* v_c_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_110_, v_a_113_, v_b_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_117_, lean_object* v_inst_118_, lean_object* v_R_119_, lean_object* v_a_120_, lean_object* v_b_121_, lean_object* v_c_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_117_, v_inst_118_, v_R_119_, v_a_120_, v_b_121_, v_c_122_);
lean_dec_ref(v_s_117_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_panic_fn_borrowed(v___x_125_, v_msg_124_);
return v___x_126_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_130_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_131_ = lean_unsigned_to_nat(4u);
v___x_132_ = lean_unsigned_to_nat(109u);
v___x_133_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_134_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_135_ = l_mkPanicMessageWithDecl(v___x_134_, v___x_133_, v___x_132_, v___x_131_, v___x_130_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_136_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = l_String_Slice_isNat(v_s_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_139_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_136_, v___x_140_, v___x_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_String_Slice_toNat_x21(v_s_142_);
lean_dec_ref(v_s_142_);
return v_res_143_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_144_){
_start:
{
lean_object* v_str_145_; lean_object* v_startInclusive_146_; lean_object* v_endExclusive_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v_decide_150_; 
v_str_145_ = lean_ctor_get(v_s_144_, 0);
v_startInclusive_146_ = lean_ctor_get(v_s_144_, 1);
v_endExclusive_147_ = lean_ctor_get(v_s_144_, 2);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_nat_sub(v_endExclusive_147_, v_startInclusive_146_);
v_decide_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
lean_dec(v___x_149_);
if (v_decide_150_ == 0)
{
uint32_t v___x_151_; uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_151_ = 45;
v___x_152_ = lean_string_utf8_get_fast(v_str_145_, v_startInclusive_146_);
v___x_153_ = lean_uint32_dec_eq(v___x_152_, v___x_151_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = l_String_Slice_isNat(v_s_144_);
lean_dec_ref(v_s_144_);
return v___x_154_;
}
else
{
lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_165_; 
lean_inc(v_endExclusive_147_);
lean_inc(v_startInclusive_146_);
lean_inc_ref(v_str_145_);
v_isSharedCheck_165_ = !lean_is_exclusive(v_s_144_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; lean_object* v_unused_167_; lean_object* v_unused_168_; 
v_unused_166_ = lean_ctor_get(v_s_144_, 2);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_s_144_, 1);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_s_144_, 0);
lean_dec(v_unused_168_);
v___x_156_ = v_s_144_;
v_isShared_157_ = v_isSharedCheck_165_;
goto v_resetjp_155_;
}
else
{
lean_dec(v_s_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_165_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_158_ = lean_string_utf8_next_fast(v_str_145_, v_startInclusive_146_);
v___x_159_ = lean_nat_sub(v___x_158_, v_startInclusive_146_);
v___x_160_ = lean_nat_add(v_startInclusive_146_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v_startInclusive_146_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_160_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_str_145_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_endExclusive_147_);
v___x_162_ = v_reuseFailAlloc_164_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
uint8_t v___x_163_; 
v___x_163_ = l_String_Slice_isNat(v___x_162_);
lean_dec_ref(v___x_162_);
return v___x_163_;
}
}
}
}
else
{
uint8_t v___x_169_; 
v___x_169_ = l_String_Slice_isNat(v_s_144_);
lean_dec_ref(v_s_144_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_String_Slice_isInt(v_s_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_173_){
_start:
{
lean_object* v_str_186_; lean_object* v_startInclusive_187_; lean_object* v_endExclusive_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v_decide_191_; 
v_str_186_ = lean_ctor_get(v_s_173_, 0);
v_startInclusive_187_ = lean_ctor_get(v_s_173_, 1);
v_endExclusive_188_ = lean_ctor_get(v_s_173_, 2);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_nat_sub(v_endExclusive_188_, v_startInclusive_187_);
v_decide_191_ = lean_nat_dec_eq(v___x_189_, v___x_190_);
lean_dec(v___x_190_);
if (v_decide_191_ == 0)
{
uint32_t v___x_192_; uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_192_ = 45;
v___x_193_ = lean_string_utf8_get_fast(v_str_186_, v_startInclusive_187_);
v___x_194_ = lean_uint32_dec_eq(v___x_193_, v___x_192_);
if (v___x_194_ == 0)
{
goto v___jp_174_;
}
else
{
lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_215_; 
lean_inc(v_endExclusive_188_);
lean_inc(v_startInclusive_187_);
lean_inc_ref(v_str_186_);
v_isSharedCheck_215_ = !lean_is_exclusive(v_s_173_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_216_ = lean_ctor_get(v_s_173_, 2);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_s_173_, 1);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_s_173_, 0);
lean_dec(v_unused_218_);
v___x_196_ = v_s_173_;
v_isShared_197_ = v_isSharedCheck_215_;
goto v_resetjp_195_;
}
else
{
lean_dec(v_s_173_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_215_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_198_ = lean_string_utf8_next_fast(v_str_186_, v_startInclusive_187_);
v___x_199_ = lean_nat_sub(v___x_198_, v_startInclusive_187_);
v___x_200_ = lean_nat_add(v_startInclusive_187_, v___x_199_);
lean_dec(v___x_199_);
lean_dec(v_startInclusive_187_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_200_);
v___x_202_ = v___x_196_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_str_186_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_endExclusive_188_);
v___x_202_ = v_reuseFailAlloc_214_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = l_String_Slice_toNat_x3f(v___x_202_);
lean_dec_ref(v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_203_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v___x_203_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = l_Int_negOfNat(v_val_205_);
lean_dec(v_val_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
}
}
else
{
goto v___jp_174_;
}
v___jp_174_:
{
lean_object* v___x_175_; 
v___x_175_ = l_String_Slice_toNat_x3f(v_s_173_);
lean_dec_ref(v_s_173_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v___x_175_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_val_177_);
lean_dec(v___x_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_nat_to_int(v_val_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_String_Slice_toInt_x3f(v_s_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Int_instInhabited;
v___x_223_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_224_ = l_panic___redArg(v___x_222_, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_221_, 1);
return v_val_225_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice_Pattern(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Slice_Numeric(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Slice_Numeric(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice_Pattern(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Slice_Numeric(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Numeric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Slice_Numeric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Slice_Numeric(builtin);
}
#ifdef __cplusplus
}
#endif
