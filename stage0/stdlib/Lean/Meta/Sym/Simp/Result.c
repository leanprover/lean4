// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Result
// Imports: public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.InferType
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
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_Result_isRfl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isRfl___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkEqTrans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkEqTrans___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_markAsDone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_Result_isRfl(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
uint8_t v_done_2_; 
v_done_2_ = lean_ctor_get_uint8(v_x_1_, 0);
if (v_done_2_ == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isRfl___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Lean_Meta_Sym_Simp_Result_isRfl(v_x_6_);
lean_dec_ref(v_x_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object* v_e_u2081_14_, lean_object* v_e_u2082_15_, lean_object* v_h_u2081_16_, lean_object* v_e_u2083_17_, lean_object* v_h_u2082_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_26_; 
lean_inc_ref(v_e_u2081_14_);
v___x_26_ = l_Lean_Meta_Sym_inferType(v_e_u2081_14_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc_n(v_a_27_, 2);
lean_dec_ref_known(v___x_26_, 1);
v___x_28_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_27_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_41_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_41_ == 0)
{
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_41_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_41_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_33_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2));
v___x_34_ = lean_box(0);
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v_a_29_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = l_Lean_mkConst(v___x_33_, v___x_35_);
v___x_37_ = l_Lean_mkApp6(v___x_36_, v_a_27_, v_e_u2081_14_, v_e_u2082_15_, v_e_u2083_17_, v_h_u2081_16_, v_h_u2082_18_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_37_);
v___x_39_ = v___x_31_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec(v_a_27_);
lean_dec_ref(v_h_u2082_18_);
lean_dec_ref(v_e_u2083_17_);
lean_dec_ref(v_h_u2081_16_);
lean_dec_ref(v_e_u2082_15_);
lean_dec_ref(v_e_u2081_14_);
v_a_42_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_28_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_28_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2082_18_);
lean_dec_ref(v_e_u2083_17_);
lean_dec_ref(v_h_u2081_16_);
lean_dec_ref(v_e_u2082_15_);
lean_dec_ref(v_e_u2081_14_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___boxed(lean_object* v_e_u2081_50_, lean_object* v_e_u2082_51_, lean_object* v_h_u2081_52_, lean_object* v_e_u2083_53_, lean_object* v_h_u2082_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_50_, v_e_u2082_51_, v_h_u2081_52_, v_e_u2083_53_, v_h_u2082_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult(lean_object* v_e_u2081_63_, lean_object* v_e_u2082_64_, lean_object* v_h_u2081_65_, lean_object* v_r_u2082_66_, uint8_t v_cd_u2081_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
if (lean_obj_tag(v_r_u2082_66_) == 0)
{
uint8_t v_done_75_; uint8_t v_contextDependent_76_; uint8_t v___y_78_; 
lean_dec_ref(v_e_u2081_63_);
v_done_75_ = lean_ctor_get_uint8(v_r_u2082_66_, 0);
v_contextDependent_76_ = lean_ctor_get_uint8(v_r_u2082_66_, 1);
lean_dec_ref_known(v_r_u2082_66_, 0);
if (v_cd_u2081_67_ == 0)
{
v___y_78_ = v_contextDependent_76_;
goto v___jp_77_;
}
else
{
v___y_78_ = v_cd_u2081_67_;
goto v___jp_77_;
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_79_, 0, v_e_u2082_64_);
lean_ctor_set(v___x_79_, 1, v_h_u2081_65_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*2, v_done_75_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*2 + 1, v___y_78_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
else
{
lean_object* v_e_x27_81_; lean_object* v_proof_82_; uint8_t v_done_83_; uint8_t v_contextDependent_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_110_; 
v_e_x27_81_ = lean_ctor_get(v_r_u2082_66_, 0);
v_proof_82_ = lean_ctor_get(v_r_u2082_66_, 1);
v_done_83_ = lean_ctor_get_uint8(v_r_u2082_66_, sizeof(void*)*2);
v_contextDependent_84_ = lean_ctor_get_uint8(v_r_u2082_66_, sizeof(void*)*2 + 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v_r_u2082_66_);
if (v_isSharedCheck_110_ == 0)
{
v___x_86_ = v_r_u2082_66_;
v_isShared_87_ = v_isSharedCheck_110_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_proof_82_);
lean_inc(v_e_x27_81_);
lean_dec(v_r_u2082_66_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_110_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; 
lean_inc_ref(v_e_x27_81_);
v___x_88_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_63_, v_e_u2082_64_, v_h_u2081_65_, v_e_x27_81_, v_proof_82_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_101_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_101_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_101_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_101_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
uint8_t v___y_94_; 
if (v_cd_u2081_67_ == 0)
{
v___y_94_ = v_contextDependent_84_;
goto v___jp_93_;
}
else
{
v___y_94_ = v_cd_u2081_67_;
goto v___jp_93_;
}
v___jp_93_:
{
lean_object* v___x_96_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_a_89_);
v___x_96_ = v___x_86_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_e_x27_81_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_a_89_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*2, v_done_83_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*2 + 1, v___y_94_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_96_);
v___x_98_ = v___x_91_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_del_object(v___x_86_);
lean_dec_ref(v_e_x27_81_);
v_a_102_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_88_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_88_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___boxed(lean_object* v_e_u2081_111_, lean_object* v_e_u2082_112_, lean_object* v_h_u2081_113_, lean_object* v_r_u2082_114_, lean_object* v_cd_u2081_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
uint8_t v_cd_u2081_boxed_123_; lean_object* v_res_124_; 
v_cd_u2081_boxed_123_ = lean_unbox(v_cd_u2081_115_);
v_res_124_ = l_Lean_Meta_Sym_Simp_mkEqTransResult(v_e_u2081_111_, v_e_u2082_112_, v_h_u2081_113_, v_r_u2082_114_, v_cd_u2081_boxed_123_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_markAsDone(lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
uint8_t v_contextDependent_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_134_; 
v_contextDependent_126_ = lean_ctor_get_uint8(v_x_125_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_134_ == 0)
{
v___x_128_ = v_x_125_;
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
else
{
lean_dec(v_x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
uint8_t v___x_130_; lean_object* v___x_132_; 
v___x_130_ = 1;
if (v_isShared_129_ == 0)
{
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_133_, 1, v_contextDependent_126_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_ctor_set_uint8(v___x_132_, 0, v___x_130_);
return v___x_132_;
}
}
}
else
{
lean_object* v_e_x27_135_; lean_object* v_proof_136_; uint8_t v_contextDependent_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
v_e_x27_135_ = lean_ctor_get(v_x_125_, 0);
v_proof_136_ = lean_ctor_get(v_x_125_, 1);
v_contextDependent_137_ = lean_ctor_get_uint8(v_x_125_, sizeof(void*)*2 + 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_145_ == 0)
{
v___x_139_ = v_x_125_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_proof_136_);
lean_inc(v_e_x27_135_);
lean_dec(v_x_125_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint8_t v___x_141_; lean_object* v___x_143_; 
v___x_141_ = 1;
if (v_isShared_140_ == 0)
{
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_e_x27_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_proof_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, sizeof(void*)*2 + 1, v_contextDependent_137_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*2, v___x_141_);
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_inc_ref(v_x_146_);
return v_x_146_;
}
else
{
lean_object* v_e_x27_148_; 
v_e_x27_148_ = lean_ctor_get(v_x_147_, 0);
lean_inc_ref(v_e_x27_148_);
return v_e_x27_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr___boxed(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_x_149_, v_x_150_);
lean_dec_ref(v_x_150_);
lean_dec_ref(v_x_149_);
return v_res_151_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Result(builtin);
}
#ifdef __cplusplus
}
#endif
