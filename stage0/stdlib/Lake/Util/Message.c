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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___y_81_; uint8_t v___y_82_; lean_object* v___y_86_; uint32_t v___y_87_; lean_object* v_str_92_; lean_object* v_str_105_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_119_ = lean_string_dec_eq(v_caption_75_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_str_122_; 
v___x_120_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__4));
v___x_121_ = lean_string_append(v_caption_75_, v___x_120_);
v_str_122_ = lean_string_append(v___x_121_, v_body_76_);
lean_dec_ref(v_body_76_);
v_str_105_ = v_str_122_;
goto v___jp_104_;
}
else
{
lean_dec_ref(v_caption_75_);
v_str_105_ = v_body_76_;
goto v___jp_104_;
}
v___jp_80_:
{
if (v___y_82_ == 0)
{
return v___y_81_;
}
else
{
lean_object* v___x_83_; lean_object* v_str_84_; 
v___x_83_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__0));
v_str_84_ = lean_string_append(v___y_81_, v___x_83_);
return v_str_84_;
}
}
v___jp_85_:
{
uint32_t v___x_88_; uint8_t v___x_89_; uint8_t v___x_90_; 
v___x_88_ = 10;
v___x_89_ = lean_uint32_dec_eq(v___y_87_, v___x_88_);
v___x_90_ = lean_bool_not(v___x_89_);
v___y_81_ = v___y_86_;
v___y_82_ = v___x_90_;
goto v___jp_80_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_string_utf8_byte_size(v_str_92_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_eq(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_inc_ref(v_str_92_);
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v_str_92_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
v___x_97_ = l_String_Slice_Pos_prev_x3f(v___x_96_, v___x_93_);
if (lean_obj_tag(v___x_97_) == 0)
{
uint32_t v___x_98_; 
lean_dec_ref_known(v___x_96_, 3);
v___x_98_ = 65;
v___y_86_ = v_str_92_;
v___y_87_ = v___x_98_;
goto v___jp_85_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_100_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_97_, 1);
v___x_100_ = l_String_Slice_Pos_get_x3f(v___x_96_, v_val_99_);
lean_dec(v_val_99_);
lean_dec_ref_known(v___x_96_, 3);
if (lean_obj_tag(v___x_100_) == 0)
{
uint32_t v___x_101_; 
v___x_101_ = 65;
v___y_86_ = v_str_92_;
v___y_87_ = v___x_101_;
goto v___jp_85_;
}
else
{
lean_object* v_val_102_; uint32_t v___x_103_; 
v_val_102_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v___x_100_, 1);
v___x_103_ = lean_unbox_uint32(v_val_102_);
lean_dec(v_val_102_);
v___y_86_ = v_str_92_;
v___y_87_ = v___x_103_;
goto v___jp_85_;
}
}
}
else
{
v___y_81_ = v_str_92_;
v___y_82_ = v___x_95_;
goto v___jp_80_;
}
}
v___jp_104_:
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
v_str_92_ = v_str_105_;
goto v___jp_91_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_str_109_; 
v___x_106_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__1));
v___x_107_ = lean_box(0);
v___x_108_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_106_, v_endPos_x3f_78_, v___x_107_, v___x_107_);
v_str_109_ = lean_string_append(v___x_108_, v_str_105_);
lean_dec_ref(v_str_105_);
v_str_92_ = v_str_109_;
goto v___jp_91_;
}
}
case 1:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_str_113_; 
v___x_110_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__2));
v___x_111_ = lean_box(0);
v___x_112_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_110_, v_endPos_x3f_78_, v___x_111_, v___x_111_);
v_str_113_ = lean_string_append(v___x_112_, v_str_105_);
lean_dec_ref(v_str_105_);
v_str_92_ = v_str_113_;
goto v___jp_91_;
}
default: 
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_str_117_; 
v___x_114_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__3));
v___x_115_ = lean_box(0);
v___x_116_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_114_, v_endPos_x3f_78_, v___x_115_, v___x_115_);
v_str_117_ = lean_string_append(v___x_116_, v_str_105_);
lean_dec_ref(v_str_105_);
v_str_92_ = v_str_117_;
goto v___jp_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object* v_severity_123_, lean_object* v_fileName_124_, lean_object* v_caption_125_, lean_object* v_body_126_, lean_object* v_pos_127_, lean_object* v_endPos_x3f_128_, lean_object* v_infoWithPos_129_){
_start:
{
uint8_t v_severity_boxed_130_; uint8_t v_infoWithPos_boxed_131_; lean_object* v_res_132_; 
v_severity_boxed_130_ = lean_unbox(v_severity_123_);
v_infoWithPos_boxed_131_ = lean_unbox(v_infoWithPos_129_);
v_res_132_ = l_Lake_mkMessageStringCore(v_severity_boxed_130_, v_fileName_124_, v_caption_125_, v_body_126_, v_pos_127_, v_endPos_x3f_128_, v_infoWithPos_boxed_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object* v_msg_133_, uint8_t v_includeEndPos_134_, uint8_t v_infoWithPos_135_){
_start:
{
lean_object* v___y_138_; 
if (v_includeEndPos_134_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_box(0);
v___y_138_ = v___x_146_;
goto v___jp_137_;
}
else
{
lean_object* v_endPos_147_; 
v_endPos_147_ = lean_ctor_get(v_msg_133_, 2);
lean_inc(v_endPos_147_);
v___y_138_ = v_endPos_147_;
goto v___jp_137_;
}
v___jp_137_:
{
lean_object* v_fileName_139_; lean_object* v_pos_140_; uint8_t v_severity_141_; lean_object* v_caption_142_; lean_object* v_data_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_fileName_139_ = lean_ctor_get(v_msg_133_, 0);
lean_inc_ref(v_fileName_139_);
v_pos_140_ = lean_ctor_get(v_msg_133_, 1);
lean_inc_ref(v_pos_140_);
v_severity_141_ = lean_ctor_get_uint8(v_msg_133_, sizeof(void*)*5 + 1);
v_caption_142_ = lean_ctor_get(v_msg_133_, 3);
lean_inc_ref(v_caption_142_);
v_data_143_ = lean_ctor_get(v_msg_133_, 4);
lean_inc(v_data_143_);
lean_dec_ref(v_msg_133_);
v___x_144_ = l_Lean_MessageData_toString(v_data_143_);
v___x_145_ = l_Lake_mkMessageStringCore(v_severity_141_, v_fileName_139_, v_caption_142_, v___x_144_, v_pos_140_, v___y_138_, v_infoWithPos_135_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object* v_msg_148_, lean_object* v_includeEndPos_149_, lean_object* v_infoWithPos_150_, lean_object* v_a_151_){
_start:
{
uint8_t v_includeEndPos_boxed_152_; uint8_t v_infoWithPos_boxed_153_; lean_object* v_res_154_; 
v_includeEndPos_boxed_152_ = lean_unbox(v_includeEndPos_149_);
v_infoWithPos_boxed_153_ = lean_unbox(v_infoWithPos_150_);
v_res_154_ = l_Lake_mkMessageString(v_msg_148_, v_includeEndPos_boxed_152_, v_infoWithPos_boxed_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
return v_x_155_;
}
else
{
lean_object* v_head_158_; lean_object* v_tail_159_; uint8_t v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_head_158_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_158_);
v_tail_159_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_tail_159_);
lean_dec_ref_known(v_x_156_, 2);
v___x_160_ = 0;
v___x_161_ = 1;
v___x_162_ = l_Lake_mkMessageString(v_head_158_, v___x_160_, v___x_161_);
v___x_163_ = lean_string_append(v_x_155_, v___x_162_);
lean_dec_ref(v___x_162_);
v_x_155_ = v___x_163_;
v_x_156_ = v_tail_159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v_x_165_, v_x_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object* v_log_169_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_172_ = l_Lean_MessageLog_toList(v_log_169_);
v___x_173_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object* v_log_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lake_mkMessageLogString(v_log_174_);
lean_dec_ref(v_log_174_);
return v_res_176_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
