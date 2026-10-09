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
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_markAsNotDone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_Simp_Result_isRfl(lean_object* v_x_1_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Result_isRfl_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Lean_Meta_Sym_Simp_Result_isRfl(v_x_1_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_isRfl___boxed(lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Meta_Sym_Simp_Result_isRfl(v_x_7_);
lean_dec_ref(v_x_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object* v_e_u2081_15_, lean_object* v_e_u2082_16_, lean_object* v_h_u2081_17_, lean_object* v_e_u2083_18_, lean_object* v_h_u2082_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; 
lean_inc_ref(v_e_u2081_15_);
v___x_27_ = l_Lean_Meta_Sym_inferType(v_e_u2081_15_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_29_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_n(v_a_28_, 2);
lean_dec_ref_known(v___x_27_, 1);
v___x_29_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_28_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_42_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_42_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_42_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_42_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_34_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkEqTrans___closed__2));
v___x_35_ = lean_box(0);
v___x_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_36_, 0, v_a_30_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = l_Lean_mkConst(v___x_34_, v___x_36_);
v___x_38_ = l_Lean_mkApp6(v___x_37_, v_a_28_, v_e_u2081_15_, v_e_u2082_16_, v_e_u2083_18_, v_h_u2081_17_, v_h_u2082_19_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_38_);
v___x_40_ = v___x_32_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
lean_dec(v_a_28_);
lean_dec_ref(v_h_u2082_19_);
lean_dec_ref(v_e_u2083_18_);
lean_dec_ref(v_h_u2081_17_);
lean_dec_ref(v_e_u2082_16_);
lean_dec_ref(v_e_u2081_15_);
v_a_43_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_29_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_29_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2082_19_);
lean_dec_ref(v_e_u2083_18_);
lean_dec_ref(v_h_u2081_17_);
lean_dec_ref(v_e_u2082_16_);
lean_dec_ref(v_e_u2081_15_);
return v___x_27_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkEqTrans_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_15_ = stack[0].m_obj;
lean_object* v_e_u2082_16_ = stack[1].m_obj;
lean_object* v_h_u2081_17_ = stack[2].m_obj;
lean_object* v_e_u2083_18_ = stack[3].m_obj;
lean_object* v_h_u2082_19_ = stack[4].m_obj;
lean_object* v_a_20_ = stack[5].m_obj;
lean_object* v_a_21_ = stack[6].m_obj;
lean_object* v_a_22_ = stack[7].m_obj;
lean_object* v_a_23_ = stack[8].m_obj;
lean_object* v_a_24_ = stack[9].m_obj;
lean_object* v_a_25_ = stack[10].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_15_, v_e_u2082_16_, v_h_u2081_17_, v_e_u2083_18_, v_h_u2082_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___boxed(lean_object* v_e_u2081_52_, lean_object* v_e_u2082_53_, lean_object* v_h_u2081_54_, lean_object* v_e_u2083_55_, lean_object* v_h_u2082_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_52_, v_e_u2082_53_, v_h_u2081_54_, v_e_u2083_55_, v_h_u2082_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_64_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult(lean_object* v_e_u2081_65_, lean_object* v_e_u2082_66_, lean_object* v_h_u2081_67_, lean_object* v_r_u2082_68_, uint8_t v_cd_u2081_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
if (lean_obj_tag(v_r_u2082_68_) == 0)
{
uint8_t v_done_77_; uint8_t v_contextDependent_78_; uint8_t v___y_80_; 
lean_dec_ref(v_e_u2081_65_);
v_done_77_ = lean_ctor_get_uint8(v_r_u2082_68_, 0);
v_contextDependent_78_ = lean_ctor_get_uint8(v_r_u2082_68_, 1);
lean_dec_ref_known(v_r_u2082_68_, 0);
if (v_cd_u2081_69_ == 0)
{
v___y_80_ = v_contextDependent_78_;
goto v___jp_79_;
}
else
{
v___y_80_ = v_cd_u2081_69_;
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_81_, 0, v_e_u2082_66_);
lean_ctor_set(v___x_81_, 1, v_h_u2081_67_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*2, v_done_77_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*2 + 1, v___y_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
else
{
lean_object* v_e_x27_83_; lean_object* v_proof_84_; uint8_t v_done_85_; uint8_t v_contextDependent_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_112_; 
v_e_x27_83_ = lean_ctor_get(v_r_u2082_68_, 0);
v_proof_84_ = lean_ctor_get(v_r_u2082_68_, 1);
v_done_85_ = lean_ctor_get_uint8(v_r_u2082_68_, sizeof(void*)*2);
v_contextDependent_86_ = lean_ctor_get_uint8(v_r_u2082_68_, sizeof(void*)*2 + 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_r_u2082_68_);
if (v_isSharedCheck_112_ == 0)
{
v___x_88_ = v_r_u2082_68_;
v_isShared_89_ = v_isSharedCheck_112_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_proof_84_);
lean_inc(v_e_x27_83_);
lean_dec(v_r_u2082_68_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_112_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; 
lean_inc_ref(v_e_x27_83_);
v___x_90_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_u2081_65_, v_e_u2082_66_, v_h_u2081_67_, v_e_x27_83_, v_proof_84_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_103_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_103_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_103_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_103_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint8_t v___y_96_; 
if (v_cd_u2081_69_ == 0)
{
v___y_96_ = v_contextDependent_86_;
goto v___jp_95_;
}
else
{
v___y_96_ = v_cd_u2081_69_;
goto v___jp_95_;
}
v___jp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v_a_91_);
v___x_98_ = v___x_88_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_e_x27_83_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_a_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*2, v_done_85_);
v___x_98_ = v_reuseFailAlloc_102_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*2 + 1, v___y_96_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_del_object(v___x_88_);
lean_dec_ref(v_e_x27_83_);
v_a_104_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_90_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_90_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_mkEqTransResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_65_ = stack[0].m_obj;
lean_object* v_e_u2082_66_ = stack[1].m_obj;
lean_object* v_h_u2081_67_ = stack[2].m_obj;
lean_object* v_r_u2082_68_ = stack[3].m_obj;
uint8_t v_cd_u2081_69_ = stack[4].m_num;
lean_object* v_a_70_ = stack[5].m_obj;
lean_object* v_a_71_ = stack[6].m_obj;
lean_object* v_a_72_ = stack[7].m_obj;
lean_object* v_a_73_ = stack[8].m_obj;
lean_object* v_a_74_ = stack[9].m_obj;
lean_object* v_a_75_ = stack[10].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_Meta_Sym_Simp_mkEqTransResult(v_e_u2081_65_, v_e_u2082_66_, v_h_u2081_67_, v_r_u2082_68_, v_cd_u2081_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkEqTransResult___boxed(lean_object* v_e_u2081_114_, lean_object* v_e_u2082_115_, lean_object* v_h_u2081_116_, lean_object* v_r_u2082_117_, lean_object* v_cd_u2081_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_cd_u2081_boxed_126_; lean_object* v_res_127_; 
v_cd_u2081_boxed_126_ = lean_unbox(v_cd_u2081_118_);
v_res_127_ = l_Lean_Meta_Sym_Simp_mkEqTransResult(v_e_u2081_114_, v_e_u2082_115_, v_h_u2081_116_, v_r_u2082_117_, v_cd_u2081_boxed_126_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_markAsDone(lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
uint8_t v_contextDependent_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_contextDependent_129_ = lean_ctor_get_uint8(v_x_128_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_128_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v_x_128_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_dec(v_x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
uint8_t v___x_133_; lean_object* v___x_135_; 
v___x_133_ = 1;
if (v_isShared_132_ == 0)
{
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_136_, 1, v_contextDependent_129_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_ctor_set_uint8(v___x_135_, 0, v___x_133_);
return v___x_135_;
}
}
}
else
{
lean_object* v_e_x27_138_; lean_object* v_proof_139_; uint8_t v_contextDependent_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_e_x27_138_ = lean_ctor_get(v_x_128_, 0);
v_proof_139_ = lean_ctor_get(v_x_128_, 1);
v_contextDependent_140_ = lean_ctor_get_uint8(v_x_128_, sizeof(void*)*2 + 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_128_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v_x_128_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_proof_139_);
lean_inc(v_e_x27_138_);
lean_dec(v_x_128_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
uint8_t v___x_144_; lean_object* v___x_146_; 
v___x_144_ = 1;
if (v_isShared_143_ == 0)
{
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_e_x27_138_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_proof_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_147_, sizeof(void*)*2 + 1, v_contextDependent_140_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*2, v___x_144_);
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_markAsNotDone(lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
uint8_t v_contextDependent_150_; lean_object* v___x_151_; 
v_contextDependent_150_ = lean_ctor_get_uint8(v_x_149_, 1);
lean_dec_ref_known(v_x_149_, 0);
v___x_151_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_150_);
return v___x_151_;
}
else
{
lean_object* v_e_x27_152_; lean_object* v_proof_153_; uint8_t v_contextDependent_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_e_x27_152_ = lean_ctor_get(v_x_149_, 0);
v_proof_153_ = lean_ctor_get(v_x_149_, 1);
v_contextDependent_154_ = lean_ctor_get_uint8(v_x_149_, sizeof(void*)*2 + 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v_x_149_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_proof_153_);
lean_inc(v_e_x27_152_);
lean_dec(v_x_149_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint8_t v___x_158_; lean_object* v___x_160_; 
v___x_158_ = 0;
if (v_isShared_157_ == 0)
{
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_e_x27_152_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_proof_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_161_, sizeof(void*)*2 + 1, v_contextDependent_154_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*2, v___x_158_);
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_inc_ref(v_x_163_);
return v_x_163_;
}
else
{
lean_object* v_e_x27_165_; 
v_e_x27_165_ = lean_ctor_get(v_x_164_, 0);
lean_inc_ref(v_e_x27_165_);
return v_e_x27_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr___boxed(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_x_166_, v_x_167_);
lean_dec_ref(v_x_167_);
lean_dec_ref(v_x_166_);
return v_res_168_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
