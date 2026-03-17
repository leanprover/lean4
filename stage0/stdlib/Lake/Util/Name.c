// Lean compiler output
// Module: Lake.Util.Name
// Imports: public import Lean.Data.Json public import Lake.Util.RBArray import Init.Data.Ord.UInt import all Init.Prelude import all Lean.Data.Name
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
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_empty(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object*);
static const lean_closure_object l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0 = (const lean_object*)&l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object*);
static const lean_closure_object l_Lake_OrdNameMap_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdNameMap_empty___closed__0 = (const lean_object*)&l_Lake_OrdNameMap_empty___closed__0_value;
static lean_once_cell_t l_Lake_OrdNameMap_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdNameMap_empty___closed__1;
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stringToLegalOrSimpleName(lean_object* v_s_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; 
lean_inc_ref(v_s_1_);
v___x_2_ = l_String_toName(v_s_1_);
v___x_3_ = l_Lean_Name_isAnonymous(v___x_2_);
if (v___x_3_ == 0)
{
lean_dec_ref(v_s_1_);
return v___x_2_;
}
else
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v___x_2_);
v___x_4_ = lean_box(0);
v___x_5_ = l_Lean_Name_str___override(v___x_4_, v_s_1_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object* v___y_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(1);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object* v_00_u03b1_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = ((lean_object*)(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0));
return v___x_10_;
}
}
static lean_object* _init_l_Lake_OrdNameMap_empty___closed__1(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = ((lean_object*)(l_Lake_OrdNameMap_empty___closed__0));
v___x_13_ = l_Lake_RBArray_empty(lean_box(0), lean_box(0), v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object* v_00_u03b1_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lake_OrdNameMap_empty___closed__1, &l_Lake_OrdNameMap_empty___closed__1_once, _init_l_Lake_OrdNameMap_empty___closed__1);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object* v_00_u03b1_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lake_OrdNameMap_empty___closed__1, &l_Lake_OrdNameMap_empty___closed__1_once, _init_l_Lake_OrdNameMap_empty___closed__1);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object* v_00_u03b1_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(1);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object* v_x_20_){
_start:
{
switch(lean_obj_tag(v_x_20_))
{
case 0:
{
return v_x_20_;
}
case 1:
{
lean_object* v_pre_21_; 
v_pre_21_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_pre_21_);
if (lean_obj_tag(v_pre_21_) == 0)
{
lean_dec_ref(v_x_20_);
return v_pre_21_;
}
else
{
lean_object* v_str_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_str_22_ = lean_ctor_get(v_x_20_, 1);
lean_inc_ref(v_str_22_);
lean_dec_ref(v_x_20_);
v___x_23_ = l_Lake_Name_eraseHead(v_pre_21_);
v___x_24_ = l_Lean_Name_str___override(v___x_23_, v_str_22_);
return v___x_24_;
}
}
default: 
{
lean_object* v_pre_25_; 
v_pre_25_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_pre_25_);
if (lean_obj_tag(v_pre_25_) == 0)
{
lean_dec_ref(v_x_20_);
return v_pre_25_;
}
else
{
lean_object* v_i_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_i_26_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_i_26_);
lean_dec_ref(v_x_20_);
v___x_27_ = l_Lake_Name_eraseHead(v_pre_25_);
v___x_28_ = l_Lean_Name_num___override(v___x_27_, v_i_26_);
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_31_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_apply_1(v_h__1_30_, v___x_32_);
return v___x_33_;
}
else
{
lean_object* v___x_34_; 
lean_dec(v_h__1_30_);
v___x_34_ = lean_apply_2(v_h__2_31_, v_x_29_, lean_box(0));
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object* v_motive_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_38_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__1_37_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
lean_dec(v_h__1_37_);
v___x_41_ = lean_apply_2(v_h__2_38_, v_x_36_, lean_box(0));
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
lean_object* v___x_47_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v___x_47_ = lean_apply_1(v_h__1_44_, v_x_42_);
return v___x_47_;
}
case 1:
{
lean_object* v_pre_48_; lean_object* v_str_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_pre_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_pre_48_);
v_str_49_ = lean_ctor_get(v_x_43_, 1);
lean_inc_ref(v_str_49_);
lean_dec_ref(v_x_43_);
v___x_50_ = lean_apply_3(v_h__3_46_, v_x_42_, v_pre_48_, v_str_49_);
return v___x_50_;
}
default: 
{
lean_object* v_pre_51_; lean_object* v_i_52_; lean_object* v___x_53_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v_pre_51_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_pre_51_);
v_i_52_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_i_52_);
lean_dec_ref(v_x_43_);
v___x_53_ = lean_apply_3(v_h__2_45_, v_x_42_, v_pre_51_, v_i_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter(lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_){
_start:
{
switch(lean_obj_tag(v_x_56_))
{
case 0:
{
lean_object* v___x_60_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__2_58_);
v___x_60_ = lean_apply_1(v_h__1_57_, v_x_55_);
return v___x_60_;
}
case 1:
{
lean_object* v_pre_61_; lean_object* v_str_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_58_);
lean_dec(v_h__1_57_);
v_pre_61_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_pre_61_);
v_str_62_ = lean_ctor_get(v_x_56_, 1);
lean_inc_ref(v_str_62_);
lean_dec_ref(v_x_56_);
v___x_63_ = lean_apply_3(v_h__3_59_, v_x_55_, v_pre_61_, v_str_62_);
return v___x_63_;
}
default: 
{
lean_object* v_pre_64_; lean_object* v_i_65_; lean_object* v___x_66_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__1_57_);
v_pre_64_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_pre_64_);
v_i_65_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_i_65_);
lean_dec_ref(v_x_56_);
v___x_66_ = lean_apply_3(v_h__2_58_, v_x_55_, v_pre_64_, v_i_65_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_, lean_object* v_h__3_71_){
_start:
{
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
lean_object* v___x_72_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__2_70_);
v___x_72_ = lean_apply_1(v_h__1_69_, v_x_67_);
return v___x_72_;
}
case 1:
{
lean_object* v_pre_73_; lean_object* v_str_74_; lean_object* v___x_75_; 
lean_dec(v_h__3_71_);
lean_dec(v_h__1_69_);
v_pre_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_pre_73_);
v_str_74_ = lean_ctor_get(v_x_68_, 1);
lean_inc_ref(v_str_74_);
lean_dec_ref(v_x_68_);
v___x_75_ = lean_apply_3(v_h__2_70_, v_x_67_, v_pre_73_, v_str_74_);
return v___x_75_;
}
default: 
{
lean_object* v_pre_76_; lean_object* v_i_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_70_);
lean_dec(v_h__1_69_);
v_pre_76_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_pre_76_);
v_i_77_ = lean_ctor_get(v_x_68_, 1);
lean_inc(v_i_77_);
lean_dec_ref(v_x_68_);
v___x_78_ = lean_apply_3(v_h__3_71_, v_x_67_, v_pre_76_, v_i_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter(lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(v_x_80_, v_x_81_, v_h__1_82_, v_h__2_83_, v_h__3_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_, lean_object* v_h__3_90_, lean_object* v_h__4_91_, lean_object* v_h__5_92_, lean_object* v_h__6_93_, lean_object* v_h__7_94_){
_start:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
lean_dec(v_h__7_94_);
lean_dec(v_h__6_93_);
lean_dec(v_h__5_92_);
lean_dec(v_h__4_91_);
lean_dec(v_h__3_90_);
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_89_);
v___x_95_ = lean_box(0);
v___x_96_ = lean_apply_1(v_h__1_88_, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; 
lean_dec(v_h__1_88_);
v___x_97_ = lean_apply_2(v_h__2_89_, v_x_87_, lean_box(0));
return v___x_97_;
}
}
case 1:
{
lean_dec(v_h__5_92_);
lean_dec(v_h__4_91_);
lean_dec(v_h__2_89_);
lean_dec(v_h__1_88_);
switch(lean_obj_tag(v_x_87_))
{
case 0:
{
lean_object* v___x_98_; 
lean_dec(v_h__7_94_);
lean_dec(v_h__6_93_);
v___x_98_ = lean_apply_2(v_h__3_90_, v_x_86_, lean_box(0));
return v___x_98_;
}
case 1:
{
lean_object* v_pre_99_; lean_object* v_str_100_; lean_object* v_pre_101_; lean_object* v_str_102_; lean_object* v___x_103_; 
lean_dec(v_h__6_93_);
lean_dec(v_h__3_90_);
v_pre_99_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_pre_99_);
v_str_100_ = lean_ctor_get(v_x_86_, 1);
lean_inc_ref(v_str_100_);
lean_dec_ref(v_x_86_);
v_pre_101_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_pre_101_);
v_str_102_ = lean_ctor_get(v_x_87_, 1);
lean_inc_ref(v_str_102_);
lean_dec_ref(v_x_87_);
v___x_103_ = lean_apply_4(v_h__7_94_, v_pre_99_, v_str_100_, v_pre_101_, v_str_102_);
return v___x_103_;
}
default: 
{
lean_object* v_pre_104_; lean_object* v_str_105_; lean_object* v_pre_106_; lean_object* v_i_107_; lean_object* v___x_108_; 
lean_dec(v_h__7_94_);
lean_dec(v_h__3_90_);
v_pre_104_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_pre_104_);
v_str_105_ = lean_ctor_get(v_x_86_, 1);
lean_inc_ref(v_str_105_);
lean_dec_ref(v_x_86_);
v_pre_106_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_pre_106_);
v_i_107_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_i_107_);
lean_dec_ref(v_x_87_);
v___x_108_ = lean_apply_4(v_h__6_93_, v_pre_104_, v_str_105_, v_pre_106_, v_i_107_);
return v___x_108_;
}
}
}
default: 
{
lean_dec(v_h__7_94_);
lean_dec(v_h__6_93_);
lean_dec(v_h__2_89_);
lean_dec(v_h__1_88_);
switch(lean_obj_tag(v_x_87_))
{
case 0:
{
lean_object* v___x_109_; 
lean_dec(v_h__5_92_);
lean_dec(v_h__4_91_);
v___x_109_ = lean_apply_2(v_h__3_90_, v_x_86_, lean_box(0));
return v___x_109_;
}
case 1:
{
lean_object* v_pre_110_; lean_object* v_i_111_; lean_object* v_pre_112_; lean_object* v_str_113_; lean_object* v___x_114_; 
lean_dec(v_h__4_91_);
lean_dec(v_h__3_90_);
v_pre_110_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_pre_110_);
v_i_111_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_i_111_);
lean_dec_ref(v_x_86_);
v_pre_112_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_pre_112_);
v_str_113_ = lean_ctor_get(v_x_87_, 1);
lean_inc_ref(v_str_113_);
lean_dec_ref(v_x_87_);
v___x_114_ = lean_apply_4(v_h__5_92_, v_pre_110_, v_i_111_, v_pre_112_, v_str_113_);
return v___x_114_;
}
default: 
{
lean_object* v_pre_115_; lean_object* v_i_116_; lean_object* v_pre_117_; lean_object* v_i_118_; lean_object* v___x_119_; 
lean_dec(v_h__5_92_);
lean_dec(v_h__3_90_);
v_pre_115_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_pre_115_);
v_i_116_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_i_116_);
lean_dec_ref(v_x_86_);
v_pre_117_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_pre_117_);
v_i_118_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_i_118_);
lean_dec_ref(v_x_87_);
v___x_119_ = lean_apply_4(v_h__4_91_, v_pre_115_, v_i_116_, v_pre_117_, v_i_118_);
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object* v_motive_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_, lean_object* v_h__3_125_, lean_object* v_h__4_126_, lean_object* v_h__5_127_, lean_object* v_h__6_128_, lean_object* v_h__7_129_){
_start:
{
switch(lean_obj_tag(v_x_121_))
{
case 0:
{
lean_dec(v_h__7_129_);
lean_dec(v_h__6_128_);
lean_dec(v_h__5_127_);
lean_dec(v_h__4_126_);
lean_dec(v_h__3_125_);
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_124_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__1_123_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
lean_dec(v_h__1_123_);
v___x_132_ = lean_apply_2(v_h__2_124_, v_x_122_, lean_box(0));
return v___x_132_;
}
}
case 1:
{
lean_dec(v_h__5_127_);
lean_dec(v_h__4_126_);
lean_dec(v_h__2_124_);
lean_dec(v_h__1_123_);
switch(lean_obj_tag(v_x_122_))
{
case 0:
{
lean_object* v___x_133_; 
lean_dec(v_h__7_129_);
lean_dec(v_h__6_128_);
v___x_133_ = lean_apply_2(v_h__3_125_, v_x_121_, lean_box(0));
return v___x_133_;
}
case 1:
{
lean_object* v_pre_134_; lean_object* v_str_135_; lean_object* v_pre_136_; lean_object* v_str_137_; lean_object* v___x_138_; 
lean_dec(v_h__6_128_);
lean_dec(v_h__3_125_);
v_pre_134_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_pre_134_);
v_str_135_ = lean_ctor_get(v_x_121_, 1);
lean_inc_ref(v_str_135_);
lean_dec_ref(v_x_121_);
v_pre_136_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_pre_136_);
v_str_137_ = lean_ctor_get(v_x_122_, 1);
lean_inc_ref(v_str_137_);
lean_dec_ref(v_x_122_);
v___x_138_ = lean_apply_4(v_h__7_129_, v_pre_134_, v_str_135_, v_pre_136_, v_str_137_);
return v___x_138_;
}
default: 
{
lean_object* v_pre_139_; lean_object* v_str_140_; lean_object* v_pre_141_; lean_object* v_i_142_; lean_object* v___x_143_; 
lean_dec(v_h__7_129_);
lean_dec(v_h__3_125_);
v_pre_139_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_pre_139_);
v_str_140_ = lean_ctor_get(v_x_121_, 1);
lean_inc_ref(v_str_140_);
lean_dec_ref(v_x_121_);
v_pre_141_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_pre_141_);
v_i_142_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_i_142_);
lean_dec_ref(v_x_122_);
v___x_143_ = lean_apply_4(v_h__6_128_, v_pre_139_, v_str_140_, v_pre_141_, v_i_142_);
return v___x_143_;
}
}
}
default: 
{
lean_dec(v_h__7_129_);
lean_dec(v_h__6_128_);
lean_dec(v_h__2_124_);
lean_dec(v_h__1_123_);
switch(lean_obj_tag(v_x_122_))
{
case 0:
{
lean_object* v___x_144_; 
lean_dec(v_h__5_127_);
lean_dec(v_h__4_126_);
v___x_144_ = lean_apply_2(v_h__3_125_, v_x_121_, lean_box(0));
return v___x_144_;
}
case 1:
{
lean_object* v_pre_145_; lean_object* v_i_146_; lean_object* v_pre_147_; lean_object* v_str_148_; lean_object* v___x_149_; 
lean_dec(v_h__4_126_);
lean_dec(v_h__3_125_);
v_pre_145_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_pre_145_);
v_i_146_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_i_146_);
lean_dec_ref(v_x_121_);
v_pre_147_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_pre_147_);
v_str_148_ = lean_ctor_get(v_x_122_, 1);
lean_inc_ref(v_str_148_);
lean_dec_ref(v_x_122_);
v___x_149_ = lean_apply_4(v_h__5_127_, v_pre_145_, v_i_146_, v_pre_147_, v_str_148_);
return v___x_149_;
}
default: 
{
lean_object* v_pre_150_; lean_object* v_i_151_; lean_object* v_pre_152_; lean_object* v_i_153_; lean_object* v___x_154_; 
lean_dec(v_h__5_127_);
lean_dec(v_h__3_125_);
v_pre_150_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_pre_150_);
v_i_151_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_i_151_);
lean_dec_ref(v_x_121_);
v_pre_152_ = lean_ctor_get(v_x_122_, 0);
lean_inc(v_pre_152_);
v_i_153_ = lean_ctor_get(v_x_122_, 1);
lean_inc(v_i_153_);
lean_dec_ref(v_x_122_);
v___x_154_ = lean_apply_4(v_h__4_126_, v_pre_150_, v_i_151_, v_pre_152_, v_i_153_);
return v___x_154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (v_x_155_ == 1)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_157_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_1(v_h__1_156_, v___x_158_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_156_);
v___x_160_ = lean_box(v_x_155_);
v___x_161_ = lean_apply_2(v_h__2_157_, v___x_160_, lean_box(0));
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
uint8_t v_x_17__boxed_165_; lean_object* v_res_166_; 
v_x_17__boxed_165_ = lean_unbox(v_x_162_);
v_res_166_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(v_x_17__boxed_165_, v_h__1_163_, v_h__2_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object* v_motive_167_, uint8_t v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (v_x_168_ == 1)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_h__2_170_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_1(v_h__1_169_, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_h__1_169_);
v___x_173_ = lean_box(v_x_168_);
v___x_174_ = lean_apply_2(v_h__2_170_, v___x_173_, lean_box(0));
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object* v_motive_175_, lean_object* v_x_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_){
_start:
{
uint8_t v_x_28__boxed_179_; lean_object* v_res_180_; 
v_x_28__boxed_179_ = lean_unbox(v_x_176_);
v_res_180_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(v_motive_175_, v_x_28__boxed_179_, v_h__1_177_, v_h__2_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object* v_ref_181_, lean_object* v_n_182_, uint8_t v_canonical_183_){
_start:
{
lean_object* v___x_184_; lean_object* v_ref_185_; lean_object* v___x_186_; lean_object* v_stx_187_; 
v___x_184_ = l_Lean_SourceInfo_fromRef(v_ref_181_, v_canonical_183_);
v_ref_185_ = l_Lean_Syntax_setHeadInfo(v_ref_181_, v___x_184_);
v___x_186_ = l_Lean_instQuoteNameMkStr1___private__1(v_n_182_);
v_stx_187_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_186_, v_ref_185_);
lean_dec(v_ref_185_);
return v_stx_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object* v_ref_188_, lean_object* v_n_189_, lean_object* v_canonical_190_){
_start:
{
uint8_t v_canonical_boxed_191_; lean_object* v_res_192_; 
v_canonical_boxed_191_ = lean_unbox(v_canonical_190_);
v_res_192_ = l_Lake_Name_quoteFrom(v_ref_188_, v_n_189_, v_canonical_boxed_191_);
return v_res_192_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_RBArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Name(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lake_Util_RBArray(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Name(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Name(builtin);
}
#ifdef __cplusplus
}
#endif
