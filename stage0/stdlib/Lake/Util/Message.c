// Lean compiler output
// Module: Lake.Util.Message
// Imports: public import Lean.Parser.Basic
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
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MessageLog_toList(lean_object*);
static const lean_string_object l_Lake_mkParserErrorMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_mkParserErrorMessage___closed__0 = (const lean_object*)&l_Lake_mkParserErrorMessage___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_mkMessageStringCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_mkMessageStringCore___closed__0 = (const lean_object*)&l_Lake_mkMessageStringCore___closed__0_value;
static const lean_string_object l_Lake_mkMessageStringCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "info: "};
static const lean_object* l_Lake_mkMessageStringCore___closed__1 = (const lean_object*)&l_Lake_mkMessageStringCore___closed__1_value;
static const lean_string_object l_Lake_mkMessageStringCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "warning: "};
static const lean_object* l_Lake_mkMessageStringCore___closed__2 = (const lean_object*)&l_Lake_mkMessageStringCore___closed__2_value;
static const lean_string_object l_Lake_mkMessageStringCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_mkMessageStringCore___closed__3 = (const lean_object*)&l_Lake_mkMessageStringCore___closed__3_value;
static const lean_string_object l_Lake_mkMessageStringCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l_Lake_mkMessageStringCore___closed__4 = (const lean_object*)&l_Lake_mkMessageStringCore___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage(lean_object* v_ictx_2_, lean_object* v_s_3_, lean_object* v_e_4_){
_start:
{
lean_object* v_fileName_5_; lean_object* v_fileMap_6_; lean_object* v_pos_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; uint8_t v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_fileName_5_ = lean_ctor_get(v_ictx_2_, 1);
lean_inc_ref(v_fileName_5_);
v_fileMap_6_ = lean_ctor_get(v_ictx_2_, 2);
lean_inc_ref(v_fileMap_6_);
lean_dec_ref(v_ictx_2_);
v_pos_7_ = lean_ctor_get(v_s_3_, 2);
v___x_8_ = l_Lean_FileMap_toPosition(v_fileMap_6_, v_pos_7_);
v___x_9_ = lean_box(0);
v___x_10_ = 1;
v___x_11_ = 2;
v___x_12_ = 0;
v___x_13_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_14_ = l_Lean_Parser_Error_toString(v_e_4_);
v___x_15_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
v___x_16_ = l_Lean_MessageData_ofFormat(v___x_15_);
v___x_17_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_17_, 0, v_fileName_5_);
lean_ctor_set(v___x_17_, 1, v___x_8_);
lean_ctor_set(v___x_17_, 2, v___x_9_);
lean_ctor_set(v___x_17_, 3, v___x_13_);
lean_ctor_set(v___x_17_, 4, v___x_16_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*5, v___x_10_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*5 + 1, v___x_11_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*5 + 2, v___x_12_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkParserErrorMessage___boxed(lean_object* v_ictx_18_, lean_object* v_s_19_, lean_object* v_e_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lake_mkParserErrorMessage(v_ictx_18_, v_s_19_, v_e_20_);
lean_dec_ref(v_s_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkExceptionMessage(lean_object* v_ictx_22_, lean_object* v_e_23_){
_start:
{
lean_object* v_fileName_24_; lean_object* v_fileMap_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v___y_36_; lean_object* v___x_49_; 
v_fileName_24_ = lean_ctor_get(v_ictx_22_, 1);
lean_inc_ref(v_fileName_24_);
v_fileMap_25_ = lean_ctor_get(v_ictx_22_, 2);
lean_inc_ref(v_fileMap_25_);
lean_dec_ref(v_ictx_22_);
v___x_26_ = l_Lean_Exception_getRef(v_e_23_);
v___x_27_ = 0;
v___x_49_ = l_Lean_Syntax_getPos_x3f(v___x_26_, v___x_27_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v___x_50_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___y_36_ = v___x_50_;
goto v___jp_35_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v___x_49_, 1);
v___y_36_ = v_val_51_;
goto v___jp_35_;
}
v___jp_28_:
{
uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_31_ = 2;
v___x_32_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_33_ = l_Lean_Exception_toMessageData(v_e_23_);
v___x_34_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_34_, 0, v_fileName_24_);
lean_ctor_set(v___x_34_, 1, v___y_29_);
lean_ctor_set(v___x_34_, 2, v___y_30_);
lean_ctor_set(v___x_34_, 3, v___x_32_);
lean_ctor_set(v___x_34_, 4, v___x_33_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*5, v___x_27_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*5 + 1, v___x_31_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*5 + 2, v___x_27_);
return v___x_34_;
}
v___jp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc_ref(v_fileMap_25_);
v___x_37_ = l_Lean_FileMap_toPosition(v_fileMap_25_, v___y_36_);
lean_dec(v___y_36_);
v___x_38_ = l_Lean_Syntax_getTailPos_x3f(v___x_26_, v___x_27_);
lean_dec(v___x_26_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v_fileMap_25_);
v___x_39_ = lean_box(0);
v___y_29_ = v___x_37_;
v___y_30_ = v___x_39_;
goto v___jp_28_;
}
else
{
lean_object* v_val_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_48_; 
v_val_40_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_48_ == 0)
{
v___x_42_ = v___x_38_;
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_val_40_);
lean_dec(v___x_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = l_Lean_FileMap_toPosition(v_fileMap_25_, v_val_40_);
lean_dec(v_val_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
v___y_29_ = v___x_37_;
v___y_30_ = v___x_46_;
goto v___jp_28_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos(lean_object* v_ictx_52_, lean_object* v_data_53_, uint8_t v_severity_54_){
_start:
{
lean_object* v_fileName_55_; lean_object* v_fileMap_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_fileName_55_ = lean_ctor_get(v_ictx_52_, 1);
lean_inc_ref(v_fileName_55_);
v_fileMap_56_ = lean_ctor_get(v_ictx_52_, 2);
lean_inc_ref(v_fileMap_56_);
lean_dec_ref(v_ictx_52_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Lean_FileMap_toPosition(v_fileMap_56_, v___x_57_);
v___x_59_ = lean_box(0);
v___x_60_ = 0;
v___x_61_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_62_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_62_, 0, v_fileName_55_);
lean_ctor_set(v___x_62_, 1, v___x_58_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
lean_ctor_set(v___x_62_, 3, v___x_61_);
lean_ctor_set(v___x_62_, 4, v_data_53_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*5, v___x_60_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*5 + 1, v_severity_54_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*5 + 2, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageNoPos___boxed(lean_object* v_ictx_63_, lean_object* v_data_64_, lean_object* v_severity_65_){
_start:
{
uint8_t v_severity_boxed_66_; lean_object* v_res_67_; 
v_severity_boxed_66_ = lean_unbox(v_severity_65_);
v_res_67_ = l_Lake_mkMessageNoPos(v_ictx_63_, v_data_64_, v_severity_boxed_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore(uint8_t v_severity_73_, lean_object* v_fileName_74_, lean_object* v_caption_75_, lean_object* v_body_76_, lean_object* v_pos_77_, lean_object* v_endPos_x3f_78_, uint8_t v_infoWithPos_79_){
_start:
{
lean_object* v___y_81_; lean_object* v___y_85_; uint32_t v___y_86_; lean_object* v___y_90_; lean_object* v_str_93_; lean_object* v_str_104_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_118_ = lean_string_dec_eq(v_caption_75_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_str_121_; 
v___x_119_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__4));
v___x_120_ = lean_string_append(v_caption_75_, v___x_119_);
v_str_121_ = lean_string_append(v___x_120_, v_body_76_);
lean_dec_ref(v_body_76_);
v_str_104_ = v_str_121_;
goto v___jp_103_;
}
else
{
lean_dec_ref(v_caption_75_);
v_str_104_ = v_body_76_;
goto v___jp_103_;
}
v___jp_80_:
{
lean_object* v___x_82_; lean_object* v_str_83_; 
v___x_82_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__0));
v_str_83_ = lean_string_append(v___y_81_, v___x_82_);
return v_str_83_;
}
v___jp_84_:
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 10;
v___x_88_ = lean_uint32_dec_eq(v___y_86_, v___x_87_);
if (v___x_88_ == 0)
{
v___y_81_ = v___y_85_;
goto v___jp_80_;
}
else
{
return v___y_85_;
}
}
v___jp_89_:
{
uint32_t v___x_91_; 
v___x_91_ = 65;
v___y_85_ = v___y_90_;
v___y_86_ = v___x_91_;
goto v___jp_84_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = lean_string_utf8_byte_size(v_str_93_);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_nat_dec_eq(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_inc_ref(v_str_93_);
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v_str_93_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
v___x_98_ = l_String_Slice_Pos_prev_x3f(v___x_97_, v___x_94_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_dec_ref_known(v___x_97_, 3);
v___y_90_ = v_str_93_;
goto v___jp_89_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_100_; 
v_val_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = l_String_Slice_Pos_get_x3f(v___x_97_, v_val_99_);
lean_dec(v_val_99_);
lean_dec_ref_known(v___x_97_, 3);
if (lean_obj_tag(v___x_100_) == 0)
{
v___y_90_ = v_str_93_;
goto v___jp_89_;
}
else
{
lean_object* v_val_101_; uint32_t v___x_102_; 
v_val_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_101_);
lean_dec_ref_known(v___x_100_, 1);
v___x_102_ = lean_unbox_uint32(v_val_101_);
lean_dec(v_val_101_);
v___y_85_ = v_str_93_;
v___y_86_ = v___x_102_;
goto v___jp_84_;
}
}
}
else
{
v___y_81_ = v_str_93_;
goto v___jp_80_;
}
}
v___jp_103_:
{
switch(v_severity_73_)
{
case 0:
{
if (v_infoWithPos_79_ == 0)
{
lean_dec(v_endPos_x3f_78_);
lean_dec_ref(v_pos_77_);
lean_dec_ref(v_fileName_74_);
v_str_93_ = v_str_104_;
goto v___jp_92_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_str_108_; 
v___x_105_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__1));
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_105_, v_endPos_x3f_78_, v___x_106_, v___x_106_);
v_str_108_ = lean_string_append(v___x_107_, v_str_104_);
lean_dec_ref(v_str_104_);
v_str_93_ = v_str_108_;
goto v___jp_92_;
}
}
case 1:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_str_112_; 
v___x_109_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__2));
v___x_110_ = lean_box(0);
v___x_111_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_109_, v_endPos_x3f_78_, v___x_110_, v___x_110_);
v_str_112_ = lean_string_append(v___x_111_, v_str_104_);
lean_dec_ref(v_str_104_);
v_str_93_ = v_str_112_;
goto v___jp_92_;
}
default: 
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_str_116_; 
v___x_113_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__3));
v___x_114_ = lean_box(0);
v___x_115_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_113_, v_endPos_x3f_78_, v___x_114_, v___x_114_);
v_str_116_ = lean_string_append(v___x_115_, v_str_104_);
lean_dec_ref(v_str_104_);
v_str_93_ = v_str_116_;
goto v___jp_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object* v_severity_122_, lean_object* v_fileName_123_, lean_object* v_caption_124_, lean_object* v_body_125_, lean_object* v_pos_126_, lean_object* v_endPos_x3f_127_, lean_object* v_infoWithPos_128_){
_start:
{
uint8_t v_severity_boxed_129_; uint8_t v_infoWithPos_boxed_130_; lean_object* v_res_131_; 
v_severity_boxed_129_ = lean_unbox(v_severity_122_);
v_infoWithPos_boxed_130_ = lean_unbox(v_infoWithPos_128_);
v_res_131_ = l_Lake_mkMessageStringCore(v_severity_boxed_129_, v_fileName_123_, v_caption_124_, v_body_125_, v_pos_126_, v_endPos_x3f_127_, v_infoWithPos_boxed_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object* v_msg_132_, uint8_t v_includeEndPos_133_, uint8_t v_infoWithPos_134_){
_start:
{
lean_object* v___y_137_; 
if (v_includeEndPos_133_ == 0)
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
v___y_137_ = v___x_145_;
goto v___jp_136_;
}
else
{
lean_object* v_endPos_146_; 
v_endPos_146_ = lean_ctor_get(v_msg_132_, 2);
lean_inc(v_endPos_146_);
v___y_137_ = v_endPos_146_;
goto v___jp_136_;
}
v___jp_136_:
{
lean_object* v_fileName_138_; lean_object* v_pos_139_; uint8_t v_severity_140_; lean_object* v_caption_141_; lean_object* v_data_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_fileName_138_ = lean_ctor_get(v_msg_132_, 0);
lean_inc_ref(v_fileName_138_);
v_pos_139_ = lean_ctor_get(v_msg_132_, 1);
lean_inc_ref(v_pos_139_);
v_severity_140_ = lean_ctor_get_uint8(v_msg_132_, sizeof(void*)*5 + 1);
v_caption_141_ = lean_ctor_get(v_msg_132_, 3);
lean_inc_ref(v_caption_141_);
v_data_142_ = lean_ctor_get(v_msg_132_, 4);
lean_inc(v_data_142_);
lean_dec_ref(v_msg_132_);
v___x_143_ = l_Lean_MessageData_toString(v_data_142_);
v___x_144_ = l_Lake_mkMessageStringCore(v_severity_140_, v_fileName_138_, v_caption_141_, v___x_143_, v_pos_139_, v___y_137_, v_infoWithPos_134_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object* v_msg_147_, lean_object* v_includeEndPos_148_, lean_object* v_infoWithPos_149_, lean_object* v_a_150_){
_start:
{
uint8_t v_includeEndPos_boxed_151_; uint8_t v_infoWithPos_boxed_152_; lean_object* v_res_153_; 
v_includeEndPos_boxed_151_ = lean_unbox(v_includeEndPos_148_);
v_infoWithPos_boxed_152_ = lean_unbox(v_infoWithPos_149_);
v_res_153_ = l_Lake_mkMessageString(v_msg_147_, v_includeEndPos_boxed_151_, v_infoWithPos_boxed_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
return v_x_154_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; uint8_t v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_head_157_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_head_157_);
v_tail_158_ = lean_ctor_get(v_x_155_, 1);
lean_inc(v_tail_158_);
lean_dec_ref_known(v_x_155_, 2);
v___x_159_ = 0;
v___x_160_ = 1;
v___x_161_ = l_Lake_mkMessageString(v_head_157_, v___x_159_, v___x_160_);
v___x_162_ = lean_string_append(v_x_154_, v___x_161_);
lean_dec_ref(v___x_161_);
v_x_154_ = v___x_162_;
v_x_155_ = v_tail_158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v_x_164_, v_x_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object* v_log_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_171_ = l_Lean_MessageLog_toList(v_log_168_);
v___x_172_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v___x_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object* v_log_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lake_mkMessageLogString(v_log_173_);
lean_dec_ref(v_log_173_);
return v_res_175_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Message(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Message(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Message(builtin);
}
#ifdef __cplusplus
}
#endif
