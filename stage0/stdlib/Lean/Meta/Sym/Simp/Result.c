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
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_Result_isRfl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isRfl___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object* v_e_u2081_14_, lean_object* v_e_u2082_15_, lean_object* v_h_u2081_16_, lean_object* v_e_u2083_17_, lean_object* v_h_u2082_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; 
lean_inc_ref(v_e_u2081_14_);
v___x_25_ = l_Lean_Meta_Sym_inferType___redArg(v_e_u2081_14_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v___x_27_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc_n(v_a_26_, 2);
lean_dec_ref(v___x_25_);
v___x_27_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_26_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_40_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_40_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_40_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_40_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_32_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2));
v___x_33_ = lean_box(0);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v_a_28_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = l_Lean_mkConst(v___x_32_, v___x_34_);
v___x_36_ = l_Lean_mkApp6(v___x_35_, v_a_26_, v_e_u2081_14_, v_e_u2082_15_, v_e_u2083_17_, v_h_u2081_16_, v_h_u2082_18_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_36_);
v___x_38_ = v___x_30_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_26_);
lean_dec_ref(v_h_u2082_18_);
lean_dec_ref(v_e_u2083_17_);
lean_dec_ref(v_h_u2081_16_);
lean_dec_ref(v_e_u2082_15_);
lean_dec_ref(v_e_u2081_14_);
v_a_41_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_27_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_27_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
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
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___boxed(lean_object* v_e_u2081_49_, lean_object* v_e_u2082_50_, lean_object* v_h_u2081_51_, lean_object* v_e_u2083_52_, lean_object* v_h_u2082_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_49_, v_e_u2082_50_, v_h_u2081_51_, v_e_u2083_52_, v_h_u2082_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object* v_e_u2081_61_, lean_object* v_e_u2082_62_, lean_object* v_h_u2081_63_, lean_object* v_e_u2083_64_, lean_object* v_h_u2082_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_61_, v_e_u2082_62_, v_h_u2081_63_, v_e_u2083_64_, v_h_u2082_65_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___boxed(lean_object* v_e_u2081_74_, lean_object* v_e_u2082_75_, lean_object* v_h_u2081_76_, lean_object* v_e_u2083_77_, lean_object* v_h_u2082_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_74_, v_e_u2082_75_, v_h_u2081_76_, v_e_u2083_77_, v_h_u2082_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg(lean_object* v_e_u2081_87_, lean_object* v_e_u2082_88_, lean_object* v_h_u2081_89_, lean_object* v_r_u2082_90_, uint8_t v_cd_u2081_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
if (lean_obj_tag(v_r_u2082_90_) == 0)
{
uint8_t v_done_98_; uint8_t v_contextDependent_99_; uint8_t v___y_101_; 
lean_dec_ref(v_e_u2081_87_);
v_done_98_ = lean_ctor_get_uint8(v_r_u2082_90_, 0);
v_contextDependent_99_ = lean_ctor_get_uint8(v_r_u2082_90_, 1);
lean_dec_ref(v_r_u2082_90_);
if (v_cd_u2081_91_ == 0)
{
v___y_101_ = v_contextDependent_99_;
goto v___jp_100_;
}
else
{
v___y_101_ = v_cd_u2081_91_;
goto v___jp_100_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_102_, 0, v_e_u2082_88_);
lean_ctor_set(v___x_102_, 1, v_h_u2081_89_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*2, v_done_98_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*2 + 1, v___y_101_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
else
{
lean_object* v_e_x27_104_; lean_object* v_proof_105_; uint8_t v_done_106_; uint8_t v_contextDependent_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_133_; 
v_e_x27_104_ = lean_ctor_get(v_r_u2082_90_, 0);
v_proof_105_ = lean_ctor_get(v_r_u2082_90_, 1);
v_done_106_ = lean_ctor_get_uint8(v_r_u2082_90_, sizeof(void*)*2);
v_contextDependent_107_ = lean_ctor_get_uint8(v_r_u2082_90_, sizeof(void*)*2 + 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_r_u2082_90_);
if (v_isSharedCheck_133_ == 0)
{
v___x_109_ = v_r_u2082_90_;
v_isShared_110_ = v_isSharedCheck_133_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_proof_105_);
lean_inc(v_e_x27_104_);
lean_dec(v_r_u2082_90_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_133_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; 
lean_inc_ref(v_e_x27_104_);
v___x_111_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_87_, v_e_u2082_88_, v_h_u2081_89_, v_e_x27_104_, v_proof_105_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_124_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_124_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
uint8_t v___y_117_; 
if (v_cd_u2081_91_ == 0)
{
v___y_117_ = v_contextDependent_107_;
goto v___jp_116_;
}
else
{
v___y_117_ = v_cd_u2081_91_;
goto v___jp_116_;
}
v___jp_116_:
{
lean_object* v___x_119_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_a_112_);
v___x_119_ = v___x_109_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_e_x27_104_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_123_, sizeof(void*)*2, v_done_106_);
v___x_119_ = v_reuseFailAlloc_123_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*2 + 1, v___y_117_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_119_);
v___x_121_ = v___x_114_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_del_object(v___x_109_);
lean_dec_ref(v_e_x27_104_);
v_a_125_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_111_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_111_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg___boxed(lean_object* v_e_u2081_134_, lean_object* v_e_u2082_135_, lean_object* v_h_u2081_136_, lean_object* v_r_u2082_137_, lean_object* v_cd_u2081_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
uint8_t v_cd_u2081_boxed_145_; lean_object* v_res_146_; 
v_cd_u2081_boxed_145_ = lean_unbox(v_cd_u2081_138_);
v_res_146_ = l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg(v_e_u2081_134_, v_e_u2082_135_, v_h_u2081_136_, v_r_u2082_137_, v_cd_u2081_boxed_145_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult(lean_object* v_e_u2081_147_, lean_object* v_e_u2082_148_, lean_object* v_h_u2081_149_, lean_object* v_r_u2082_150_, uint8_t v_cd_u2081_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
if (lean_obj_tag(v_r_u2082_150_) == 0)
{
uint8_t v_done_159_; uint8_t v_contextDependent_160_; uint8_t v___y_162_; 
lean_dec_ref(v_e_u2081_147_);
v_done_159_ = lean_ctor_get_uint8(v_r_u2082_150_, 0);
v_contextDependent_160_ = lean_ctor_get_uint8(v_r_u2082_150_, 1);
lean_dec_ref(v_r_u2082_150_);
if (v_cd_u2081_151_ == 0)
{
v___y_162_ = v_contextDependent_160_;
goto v___jp_161_;
}
else
{
v___y_162_ = v_cd_u2081_151_;
goto v___jp_161_;
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_163_, 0, v_e_u2082_148_);
lean_ctor_set(v___x_163_, 1, v_h_u2081_149_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*2, v_done_159_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*2 + 1, v___y_162_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
else
{
lean_object* v_e_x27_165_; lean_object* v_proof_166_; uint8_t v_done_167_; uint8_t v_contextDependent_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_194_; 
v_e_x27_165_ = lean_ctor_get(v_r_u2082_150_, 0);
v_proof_166_ = lean_ctor_get(v_r_u2082_150_, 1);
v_done_167_ = lean_ctor_get_uint8(v_r_u2082_150_, sizeof(void*)*2);
v_contextDependent_168_ = lean_ctor_get_uint8(v_r_u2082_150_, sizeof(void*)*2 + 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_r_u2082_150_);
if (v_isSharedCheck_194_ == 0)
{
v___x_170_ = v_r_u2082_150_;
v_isShared_171_ = v_isSharedCheck_194_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_proof_166_);
lean_inc(v_e_x27_165_);
lean_dec(v_r_u2082_150_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_194_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; 
lean_inc_ref(v_e_x27_165_);
v___x_172_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_u2081_147_, v_e_u2082_148_, v_h_u2081_149_, v_e_x27_165_, v_proof_166_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint8_t v___y_178_; 
if (v_cd_u2081_151_ == 0)
{
v___y_178_ = v_contextDependent_168_;
goto v___jp_177_;
}
else
{
v___y_178_ = v_cd_u2081_151_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v_a_173_);
v___x_180_ = v___x_170_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_e_x27_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_a_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*2, v_done_167_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*2 + 1, v___y_178_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_180_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_del_object(v___x_170_);
lean_dec_ref(v_e_x27_165_);
v_a_186_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_172_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_172_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___boxed(lean_object* v_e_u2081_195_, lean_object* v_e_u2082_196_, lean_object* v_h_u2081_197_, lean_object* v_r_u2082_198_, lean_object* v_cd_u2081_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
uint8_t v_cd_u2081_boxed_207_; lean_object* v_res_208_; 
v_cd_u2081_boxed_207_ = lean_unbox(v_cd_u2081_199_);
v_res_208_ = l_Lean_Meta_Sym_Simp_mkEqTransResult(v_e_u2081_195_, v_e_u2082_196_, v_h_u2081_197_, v_r_u2082_198_, v_cd_u2081_boxed_207_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_markAsDone(lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
uint8_t v_contextDependent_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_contextDependent_210_ = lean_ctor_get_uint8(v_x_209_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_218_ == 0)
{
v___x_212_ = v_x_209_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_dec(v_x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
uint8_t v___x_214_; lean_object* v___x_216_; 
v___x_214_ = 1;
if (v_isShared_213_ == 0)
{
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, 1, v_contextDependent_210_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_ctor_set_uint8(v___x_216_, 0, v___x_214_);
return v___x_216_;
}
}
}
else
{
lean_object* v_e_x27_219_; lean_object* v_proof_220_; uint8_t v_contextDependent_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_e_x27_219_ = lean_ctor_get(v_x_209_, 0);
v_proof_220_ = lean_ctor_get(v_x_209_, 1);
v_contextDependent_221_ = lean_ctor_get_uint8(v_x_209_, sizeof(void*)*2 + 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_x_209_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_proof_220_);
lean_inc(v_e_x27_219_);
lean_dec(v_x_209_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; lean_object* v___x_227_; 
v___x_225_ = 1;
if (v_isShared_224_ == 0)
{
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_e_x27_219_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_proof_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*2 + 1, v_contextDependent_221_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*2, v___x_225_);
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_inc_ref(v_x_230_);
return v_x_230_;
}
else
{
lean_object* v_e_x27_232_; 
v_e_x27_232_ = lean_ctor_get(v_x_231_, 0);
lean_inc_ref(v_e_x27_232_);
return v_e_x27_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr___boxed(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_x_233_, v_x_234_);
lean_dec_ref(v_x_234_);
lean_dec_ref(v_x_233_);
return v_res_235_;
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
