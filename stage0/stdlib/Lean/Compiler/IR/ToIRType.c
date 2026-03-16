// Lean compiler output
// Module: Lean.Compiler.IR.ToIRType
// Imports: public import Lean.Compiler.IR.Format public import Lean.Compiler.LCNF.MonoTypes
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_nameToIRType_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_nameToIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.IR.ToIRType"};
static const lean_object* l_Lean_IR_nameToIRType___closed__0 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__0_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.IR.nameToIRType"};
static const lean_object* l_Lean_IR_nameToIRType___closed__1 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__1_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_nameToIRType___closed__2 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__2_value;
static lean_once_cell_t l_Lean_IR_nameToIRType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_nameToIRType___closed__3;
static const lean_string_object l_Lean_IR_nameToIRType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_IR_nameToIRType___closed__4 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__4_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_IR_nameToIRType___closed__5 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__5_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_IR_nameToIRType___closed__6 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__6_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_IR_nameToIRType___closed__7 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__7_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_IR_nameToIRType___closed__8 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__8_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_IR_nameToIRType___closed__9 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__9_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_IR_nameToIRType___closed__10 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__10_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l_Lean_IR_nameToIRType___closed__11 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__11_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l_Lean_IR_nameToIRType___closed__12 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__12_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l_Lean_IR_nameToIRType___closed__13 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__13_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l_Lean_IR_nameToIRType___closed__14 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType___boxed(lean_object*);
static const lean_string_object l_Lean_IR_toIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.IR.toIRType"};
static const lean_object* l_Lean_IR_toIRType___closed__0 = (const lean_object*)&l_Lean_IR_toIRType___closed__0_value;
static lean_once_cell_t l_Lean_IR_toIRType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_toIRType___closed__1;
static const lean_string_object l_Lean_IR_toIRType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_IR_toIRType___closed__2 = (const lean_object*)&l_Lean_IR_toIRType___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_toIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIRType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_nameToIRType_spec__0(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_panic_fn(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_IR_nameToIRType___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__2));
v___x_8_ = lean_unsigned_to_nat(9u);
v___x_9_ = lean_unsigned_to_nat(32u);
v___x_10_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__1));
v___x_11_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__0));
v___x_12_ = l_mkPanicMessageWithDecl(v___x_11_, v___x_10_, v___x_9_, v___x_8_, v___x_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType(lean_object* v_n_24_){
_start:
{
if (lean_obj_tag(v_n_24_) == 1)
{
lean_object* v_pre_28_; 
v_pre_28_ = lean_ctor_get(v_n_24_, 0);
if (lean_obj_tag(v_pre_28_) == 0)
{
lean_object* v_str_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_str_29_ = lean_ctor_get(v_n_24_, 1);
v___x_30_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__4));
v___x_31_ = lean_string_dec_eq(v_str_29_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__5));
v___x_33_ = lean_string_dec_eq(v_str_29_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__6));
v___x_35_ = lean_string_dec_eq(v_str_29_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__7));
v___x_37_ = lean_string_dec_eq(v_str_29_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__8));
v___x_39_ = lean_string_dec_eq(v_str_29_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__9));
v___x_41_ = lean_string_dec_eq(v_str_29_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__10));
v___x_43_ = lean_string_dec_eq(v_str_29_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__11));
v___x_45_ = lean_string_dec_eq(v_str_29_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__12));
v___x_47_ = lean_string_dec_eq(v_str_29_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__13));
v___x_49_ = lean_string_dec_eq(v_str_29_, v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__14));
v___x_51_ = lean_string_dec_eq(v_str_29_, v___x_50_);
if (v___x_51_ == 0)
{
goto v___jp_25_;
}
else
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(13);
return v___x_52_;
}
}
else
{
lean_object* v___x_53_; 
v___x_53_ = lean_box(12);
return v___x_53_;
}
}
else
{
lean_object* v___x_54_; 
v___x_54_ = lean_box(8);
return v___x_54_;
}
}
else
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(7);
return v___x_55_;
}
}
else
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(6);
return v___x_56_;
}
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(4);
return v___x_57_;
}
}
else
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(3);
return v___x_58_;
}
}
else
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(2);
return v___x_59_;
}
}
else
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(1);
return v___x_60_;
}
}
else
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(9);
return v___x_61_;
}
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
else
{
goto v___jp_25_;
}
}
else
{
goto v___jp_25_;
}
v___jp_25_:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_IR_nameToIRType___closed__3, &l_Lean_IR_nameToIRType___closed__3_once, _init_l_Lean_IR_nameToIRType___closed__3);
v___x_27_ = l_panic___at___00Lean_IR_nameToIRType_spec__0(v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType___boxed(lean_object* v_n_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_IR_nameToIRType(v_n_63_);
lean_dec(v_n_63_);
return v_res_64_;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__1(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_66_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__2));
v___x_67_ = lean_unsigned_to_nat(9u);
v___x_68_ = lean_unsigned_to_nat(49u);
v___x_69_ = ((lean_object*)(l_Lean_IR_toIRType___closed__0));
v___x_70_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__0));
v___x_71_ = l_mkPanicMessageWithDecl(v___x_70_, v___x_69_, v___x_68_, v___x_67_, v___x_66_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIRType(lean_object* v_type_73_){
_start:
{
if (lean_obj_tag(v_type_73_) == 4)
{
lean_object* v_declName_77_; 
v_declName_77_ = lean_ctor_get(v_type_73_, 0);
if (lean_obj_tag(v_declName_77_) == 1)
{
lean_object* v_pre_78_; 
v_pre_78_ = lean_ctor_get(v_declName_77_, 0);
if (lean_obj_tag(v_pre_78_) == 0)
{
lean_object* v_us_79_; lean_object* v_str_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_us_79_ = lean_ctor_get(v_type_73_, 1);
v_str_80_ = lean_ctor_get(v_declName_77_, 1);
v___x_81_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__4));
v___x_82_ = lean_string_dec_eq(v_str_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__5));
v___x_84_ = lean_string_dec_eq(v_str_80_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__6));
v___x_86_ = lean_string_dec_eq(v_str_80_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__7));
v___x_88_ = lean_string_dec_eq(v_str_80_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__8));
v___x_90_ = lean_string_dec_eq(v_str_80_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__9));
v___x_92_ = lean_string_dec_eq(v_str_80_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_IR_toIRType___closed__2));
v___x_94_ = lean_string_dec_eq(v_str_80_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__10));
v___x_96_ = lean_string_dec_eq(v_str_80_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__11));
v___x_98_ = lean_string_dec_eq(v_str_80_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__12));
v___x_100_ = lean_string_dec_eq(v_str_80_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__13));
v___x_102_ = lean_string_dec_eq(v_str_80_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_IR_nameToIRType___closed__14));
v___x_104_ = lean_string_dec_eq(v_str_80_, v___x_103_);
if (v___x_104_ == 0)
{
goto v___jp_74_;
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_box(13);
return v___x_105_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(12);
return v___x_106_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(8);
return v___x_107_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(7);
return v___x_108_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(6);
return v___x_109_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(5);
return v___x_110_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_box(4);
return v___x_111_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(3);
return v___x_112_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(2);
return v___x_113_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(1);
return v___x_114_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(9);
return v___x_115_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
if (lean_obj_tag(v_us_79_) == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
goto v___jp_74_;
}
}
}
else
{
goto v___jp_74_;
}
}
else
{
goto v___jp_74_;
}
}
else
{
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_obj_once(&l_Lean_IR_toIRType___closed__1, &l_Lean_IR_toIRType___closed__1_once, _init_l_Lean_IR_toIRType___closed__1);
v___x_76_ = l_panic___at___00Lean_IR_nameToIRType_spec__0(v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIRType___boxed(lean_object* v_type_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_IR_toIRType(v_type_117_);
lean_dec_ref(v_type_117_);
return v_res_118_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_ToIRType(builtin);
}
#ifdef __cplusplus
}
#endif
