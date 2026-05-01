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
lean_dec_ref(v___x_49_);
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
lean_object* v___y_81_; lean_object* v___y_85_; uint8_t v___y_86_; uint8_t v___y_88_; lean_object* v___y_89_; uint32_t v___y_90_; lean_object* v_str_94_; lean_object* v_str_107_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_121_ = lean_string_dec_eq(v_caption_75_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_str_124_; 
v___x_122_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__4));
v___x_123_ = lean_string_append(v_caption_75_, v___x_122_);
v_str_124_ = lean_string_append(v___x_123_, v_body_76_);
lean_dec_ref(v_body_76_);
v_str_107_ = v_str_124_;
goto v___jp_106_;
}
else
{
lean_dec_ref(v_caption_75_);
v_str_107_ = v_body_76_;
goto v___jp_106_;
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
if (v___y_86_ == 0)
{
return v___y_85_;
}
else
{
v___y_81_ = v___y_85_;
goto v___jp_80_;
}
}
v___jp_87_:
{
uint32_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = 10;
v___x_92_ = lean_uint32_dec_eq(v___y_90_, v___x_91_);
if (v___x_92_ == 0)
{
v___y_81_ = v___y_89_;
goto v___jp_80_;
}
else
{
v___y_85_ = v___y_89_;
v___y_86_ = v___y_88_;
goto v___jp_84_;
}
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = lean_string_utf8_byte_size(v_str_94_);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_inc_ref(v_str_94_);
v___x_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_98_, 0, v_str_94_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_95_);
v___x_99_ = l_String_Slice_Pos_prev_x3f(v___x_98_, v___x_95_);
if (lean_obj_tag(v___x_99_) == 0)
{
uint32_t v___x_100_; 
lean_dec_ref(v___x_98_);
v___x_100_ = 65;
v___y_88_ = v___x_97_;
v___y_89_ = v_str_94_;
v___y_90_ = v___x_100_;
goto v___jp_87_;
}
else
{
lean_object* v_val_101_; lean_object* v___x_102_; 
v_val_101_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_val_101_);
lean_dec_ref(v___x_99_);
v___x_102_ = l_String_Slice_Pos_get_x3f(v___x_98_, v_val_101_);
lean_dec(v_val_101_);
lean_dec_ref(v___x_98_);
if (lean_obj_tag(v___x_102_) == 0)
{
uint32_t v___x_103_; 
v___x_103_ = 65;
v___y_88_ = v___x_97_;
v___y_89_ = v_str_94_;
v___y_90_ = v___x_103_;
goto v___jp_87_;
}
else
{
lean_object* v_val_104_; uint32_t v___x_105_; 
v_val_104_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_val_104_);
lean_dec_ref(v___x_102_);
v___x_105_ = lean_unbox_uint32(v_val_104_);
lean_dec(v_val_104_);
v___y_88_ = v___x_97_;
v___y_89_ = v_str_94_;
v___y_90_ = v___x_105_;
goto v___jp_87_;
}
}
}
else
{
v___y_85_ = v_str_94_;
v___y_86_ = v___x_97_;
goto v___jp_84_;
}
}
v___jp_106_:
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
v_str_94_ = v_str_107_;
goto v___jp_93_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_str_111_; 
v___x_108_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__1));
v___x_109_ = lean_box(0);
v___x_110_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_108_, v_endPos_x3f_78_, v___x_109_, v___x_109_);
v_str_111_ = lean_string_append(v___x_110_, v_str_107_);
lean_dec_ref(v_str_107_);
v_str_94_ = v_str_111_;
goto v___jp_93_;
}
}
case 1:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_str_115_; 
v___x_112_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__2));
v___x_113_ = lean_box(0);
v___x_114_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_112_, v_endPos_x3f_78_, v___x_113_, v___x_113_);
v_str_115_ = lean_string_append(v___x_114_, v_str_107_);
lean_dec_ref(v_str_107_);
v_str_94_ = v_str_115_;
goto v___jp_93_;
}
default: 
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_str_119_; 
v___x_116_ = ((lean_object*)(l_Lake_mkMessageStringCore___closed__3));
v___x_117_ = lean_box(0);
v___x_118_ = l_Lean_mkErrorStringWithPos(v_fileName_74_, v_pos_77_, v___x_116_, v_endPos_x3f_78_, v___x_117_, v___x_117_);
v_str_119_ = lean_string_append(v___x_118_, v_str_107_);
lean_dec_ref(v_str_107_);
v_str_94_ = v_str_119_;
goto v___jp_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageStringCore___boxed(lean_object* v_severity_125_, lean_object* v_fileName_126_, lean_object* v_caption_127_, lean_object* v_body_128_, lean_object* v_pos_129_, lean_object* v_endPos_x3f_130_, lean_object* v_infoWithPos_131_){
_start:
{
uint8_t v_severity_boxed_132_; uint8_t v_infoWithPos_boxed_133_; lean_object* v_res_134_; 
v_severity_boxed_132_ = lean_unbox(v_severity_125_);
v_infoWithPos_boxed_133_ = lean_unbox(v_infoWithPos_131_);
v_res_134_ = l_Lake_mkMessageStringCore(v_severity_boxed_132_, v_fileName_126_, v_caption_127_, v_body_128_, v_pos_129_, v_endPos_x3f_130_, v_infoWithPos_boxed_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString(lean_object* v_msg_135_, uint8_t v_includeEndPos_136_, uint8_t v_infoWithPos_137_){
_start:
{
lean_object* v___y_140_; 
if (v_includeEndPos_136_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
v___y_140_ = v___x_148_;
goto v___jp_139_;
}
else
{
lean_object* v_endPos_149_; 
v_endPos_149_ = lean_ctor_get(v_msg_135_, 2);
lean_inc(v_endPos_149_);
v___y_140_ = v_endPos_149_;
goto v___jp_139_;
}
v___jp_139_:
{
lean_object* v_fileName_141_; lean_object* v_pos_142_; uint8_t v_severity_143_; lean_object* v_caption_144_; lean_object* v_data_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_fileName_141_ = lean_ctor_get(v_msg_135_, 0);
lean_inc_ref(v_fileName_141_);
v_pos_142_ = lean_ctor_get(v_msg_135_, 1);
lean_inc_ref(v_pos_142_);
v_severity_143_ = lean_ctor_get_uint8(v_msg_135_, sizeof(void*)*5 + 1);
v_caption_144_ = lean_ctor_get(v_msg_135_, 3);
lean_inc_ref(v_caption_144_);
v_data_145_ = lean_ctor_get(v_msg_135_, 4);
lean_inc(v_data_145_);
lean_dec_ref(v_msg_135_);
v___x_146_ = l_Lean_MessageData_toString(v_data_145_);
v___x_147_ = l_Lake_mkMessageStringCore(v_severity_143_, v_fileName_141_, v_caption_144_, v___x_146_, v_pos_142_, v___y_140_, v_infoWithPos_137_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageString___boxed(lean_object* v_msg_150_, lean_object* v_includeEndPos_151_, lean_object* v_infoWithPos_152_, lean_object* v_a_153_){
_start:
{
uint8_t v_includeEndPos_boxed_154_; uint8_t v_infoWithPos_boxed_155_; lean_object* v_res_156_; 
v_includeEndPos_boxed_154_ = lean_unbox(v_includeEndPos_151_);
v_infoWithPos_boxed_155_ = lean_unbox(v_infoWithPos_152_);
v_res_156_ = l_Lake_mkMessageString(v_msg_150_, v_includeEndPos_boxed_154_, v_infoWithPos_boxed_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
return v_x_157_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; uint8_t v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_head_160_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_head_160_);
v_tail_161_ = lean_ctor_get(v_x_158_, 1);
lean_inc(v_tail_161_);
lean_dec_ref(v_x_158_);
v___x_162_ = 0;
v___x_163_ = 1;
v___x_164_ = l_Lake_mkMessageString(v_head_160_, v___x_162_, v___x_163_);
v___x_165_ = lean_string_append(v_x_157_, v___x_164_);
lean_dec_ref(v___x_164_);
v_x_157_ = v___x_165_;
v_x_158_ = v_tail_161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v_x_167_, v_x_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString(lean_object* v_log_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = ((lean_object*)(l_Lake_mkParserErrorMessage___closed__0));
v___x_174_ = l_Lean_MessageLog_toList(v_log_171_);
v___x_175_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v___x_173_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkMessageLogString___boxed(lean_object* v_log_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lake_mkMessageLogString(v_log_176_);
lean_dec_ref(v_log_176_);
return v_res_178_;
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
