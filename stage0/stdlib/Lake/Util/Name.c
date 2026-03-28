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
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Name_quoteFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Name_quoteFrom___closed__0 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__0_value;
static const lean_string_object l_Lake_Name_quoteFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Name_quoteFrom___closed__1 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__1_value;
static const lean_string_object l_Lake_Name_quoteFrom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_Name_quoteFrom___closed__2 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__2_value;
static const lean_string_object l_Lake_Name_quoteFrom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lake_Name_quoteFrom___closed__3 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__3_value;
static const lean_ctor_object l_Lake_Name_quoteFrom___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Name_quoteFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Name_quoteFrom___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Name_quoteFrom___closed__4_value_aux_0),((lean_object*)&l_Lake_Name_quoteFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Name_quoteFrom___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Name_quoteFrom___closed__4_value_aux_1),((lean_object*)&l_Lake_Name_quoteFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Name_quoteFrom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Name_quoteFrom___closed__4_value_aux_2),((lean_object*)&l_Lake_Name_quoteFrom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lake_Name_quoteFrom___closed__4 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__4_value;
static const lean_string_object l_Lake_Name_quoteFrom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake_Name_quoteFrom___closed__5 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__5_value;
static const lean_string_object l_Lake_Name_quoteFrom___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Name_quoteFrom___closed__6 = (const lean_object*)&l_Lake_Name_quoteFrom___closed__6_value;
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
switch(lean_obj_tag(v_x_81_))
{
case 0:
{
lean_object* v___x_85_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__2_83_);
v___x_85_ = lean_apply_1(v_h__1_82_, v_x_80_);
return v___x_85_;
}
case 1:
{
lean_object* v_pre_86_; lean_object* v_str_87_; lean_object* v___x_88_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__1_82_);
v_pre_86_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_pre_86_);
v_str_87_ = lean_ctor_get(v_x_81_, 1);
lean_inc_ref(v_str_87_);
lean_dec_ref(v_x_81_);
v___x_88_ = lean_apply_3(v_h__2_83_, v_x_80_, v_pre_86_, v_str_87_);
return v___x_88_;
}
default: 
{
lean_object* v_pre_89_; lean_object* v_i_90_; lean_object* v___x_91_; 
lean_dec(v_h__2_83_);
lean_dec(v_h__1_82_);
v_pre_89_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_pre_89_);
v_i_90_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_i_90_);
lean_dec_ref(v_x_81_);
v___x_91_ = lean_apply_3(v_h__3_84_, v_x_80_, v_pre_89_, v_i_90_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_, lean_object* v_h__4_97_, lean_object* v_h__5_98_, lean_object* v_h__6_99_, lean_object* v_h__7_100_){
_start:
{
switch(lean_obj_tag(v_x_92_))
{
case 0:
{
lean_dec(v_h__7_100_);
lean_dec(v_h__6_99_);
lean_dec(v_h__5_98_);
lean_dec(v_h__4_97_);
lean_dec(v_h__3_96_);
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_95_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__1_94_, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
lean_dec(v_h__1_94_);
v___x_103_ = lean_apply_2(v_h__2_95_, v_x_93_, lean_box(0));
return v___x_103_;
}
}
case 1:
{
lean_dec(v_h__5_98_);
lean_dec(v_h__4_97_);
lean_dec(v_h__2_95_);
lean_dec(v_h__1_94_);
switch(lean_obj_tag(v_x_93_))
{
case 0:
{
lean_object* v___x_104_; 
lean_dec(v_h__7_100_);
lean_dec(v_h__6_99_);
v___x_104_ = lean_apply_2(v_h__3_96_, v_x_92_, lean_box(0));
return v___x_104_;
}
case 1:
{
lean_object* v_pre_105_; lean_object* v_str_106_; lean_object* v_pre_107_; lean_object* v_str_108_; lean_object* v___x_109_; 
lean_dec(v_h__6_99_);
lean_dec(v_h__3_96_);
v_pre_105_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_pre_105_);
v_str_106_ = lean_ctor_get(v_x_92_, 1);
lean_inc_ref(v_str_106_);
lean_dec_ref(v_x_92_);
v_pre_107_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_pre_107_);
v_str_108_ = lean_ctor_get(v_x_93_, 1);
lean_inc_ref(v_str_108_);
lean_dec_ref(v_x_93_);
v___x_109_ = lean_apply_4(v_h__7_100_, v_pre_105_, v_str_106_, v_pre_107_, v_str_108_);
return v___x_109_;
}
default: 
{
lean_object* v_pre_110_; lean_object* v_str_111_; lean_object* v_pre_112_; lean_object* v_i_113_; lean_object* v___x_114_; 
lean_dec(v_h__7_100_);
lean_dec(v_h__3_96_);
v_pre_110_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_pre_110_);
v_str_111_ = lean_ctor_get(v_x_92_, 1);
lean_inc_ref(v_str_111_);
lean_dec_ref(v_x_92_);
v_pre_112_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_pre_112_);
v_i_113_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_i_113_);
lean_dec_ref(v_x_93_);
v___x_114_ = lean_apply_4(v_h__6_99_, v_pre_110_, v_str_111_, v_pre_112_, v_i_113_);
return v___x_114_;
}
}
}
default: 
{
lean_dec(v_h__7_100_);
lean_dec(v_h__6_99_);
lean_dec(v_h__2_95_);
lean_dec(v_h__1_94_);
switch(lean_obj_tag(v_x_93_))
{
case 0:
{
lean_object* v___x_115_; 
lean_dec(v_h__5_98_);
lean_dec(v_h__4_97_);
v___x_115_ = lean_apply_2(v_h__3_96_, v_x_92_, lean_box(0));
return v___x_115_;
}
case 1:
{
lean_object* v_pre_116_; lean_object* v_i_117_; lean_object* v_pre_118_; lean_object* v_str_119_; lean_object* v___x_120_; 
lean_dec(v_h__4_97_);
lean_dec(v_h__3_96_);
v_pre_116_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_pre_116_);
v_i_117_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_i_117_);
lean_dec_ref(v_x_92_);
v_pre_118_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_pre_118_);
v_str_119_ = lean_ctor_get(v_x_93_, 1);
lean_inc_ref(v_str_119_);
lean_dec_ref(v_x_93_);
v___x_120_ = lean_apply_4(v_h__5_98_, v_pre_116_, v_i_117_, v_pre_118_, v_str_119_);
return v___x_120_;
}
default: 
{
lean_object* v_pre_121_; lean_object* v_i_122_; lean_object* v_pre_123_; lean_object* v_i_124_; lean_object* v___x_125_; 
lean_dec(v_h__5_98_);
lean_dec(v_h__3_96_);
v_pre_121_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_pre_121_);
v_i_122_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_i_122_);
lean_dec_ref(v_x_92_);
v_pre_123_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_pre_123_);
v_i_124_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_i_124_);
lean_dec_ref(v_x_93_);
v___x_125_ = lean_apply_4(v_h__4_97_, v_pre_121_, v_i_122_, v_pre_123_, v_i_124_);
return v___x_125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object* v_motive_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_, lean_object* v_h__3_131_, lean_object* v_h__4_132_, lean_object* v_h__5_133_, lean_object* v_h__6_134_, lean_object* v_h__7_135_){
_start:
{
switch(lean_obj_tag(v_x_127_))
{
case 0:
{
lean_dec(v_h__7_135_);
lean_dec(v_h__6_134_);
lean_dec(v_h__5_133_);
lean_dec(v_h__4_132_);
lean_dec(v_h__3_131_);
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_130_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_1(v_h__1_129_, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; 
lean_dec(v_h__1_129_);
v___x_138_ = lean_apply_2(v_h__2_130_, v_x_128_, lean_box(0));
return v___x_138_;
}
}
case 1:
{
lean_dec(v_h__5_133_);
lean_dec(v_h__4_132_);
lean_dec(v_h__2_130_);
lean_dec(v_h__1_129_);
switch(lean_obj_tag(v_x_128_))
{
case 0:
{
lean_object* v___x_139_; 
lean_dec(v_h__7_135_);
lean_dec(v_h__6_134_);
v___x_139_ = lean_apply_2(v_h__3_131_, v_x_127_, lean_box(0));
return v___x_139_;
}
case 1:
{
lean_object* v_pre_140_; lean_object* v_str_141_; lean_object* v_pre_142_; lean_object* v_str_143_; lean_object* v___x_144_; 
lean_dec(v_h__6_134_);
lean_dec(v_h__3_131_);
v_pre_140_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_pre_140_);
v_str_141_ = lean_ctor_get(v_x_127_, 1);
lean_inc_ref(v_str_141_);
lean_dec_ref(v_x_127_);
v_pre_142_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_pre_142_);
v_str_143_ = lean_ctor_get(v_x_128_, 1);
lean_inc_ref(v_str_143_);
lean_dec_ref(v_x_128_);
v___x_144_ = lean_apply_4(v_h__7_135_, v_pre_140_, v_str_141_, v_pre_142_, v_str_143_);
return v___x_144_;
}
default: 
{
lean_object* v_pre_145_; lean_object* v_str_146_; lean_object* v_pre_147_; lean_object* v_i_148_; lean_object* v___x_149_; 
lean_dec(v_h__7_135_);
lean_dec(v_h__3_131_);
v_pre_145_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_pre_145_);
v_str_146_ = lean_ctor_get(v_x_127_, 1);
lean_inc_ref(v_str_146_);
lean_dec_ref(v_x_127_);
v_pre_147_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_pre_147_);
v_i_148_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_i_148_);
lean_dec_ref(v_x_128_);
v___x_149_ = lean_apply_4(v_h__6_134_, v_pre_145_, v_str_146_, v_pre_147_, v_i_148_);
return v___x_149_;
}
}
}
default: 
{
lean_dec(v_h__7_135_);
lean_dec(v_h__6_134_);
lean_dec(v_h__2_130_);
lean_dec(v_h__1_129_);
switch(lean_obj_tag(v_x_128_))
{
case 0:
{
lean_object* v___x_150_; 
lean_dec(v_h__5_133_);
lean_dec(v_h__4_132_);
v___x_150_ = lean_apply_2(v_h__3_131_, v_x_127_, lean_box(0));
return v___x_150_;
}
case 1:
{
lean_object* v_pre_151_; lean_object* v_i_152_; lean_object* v_pre_153_; lean_object* v_str_154_; lean_object* v___x_155_; 
lean_dec(v_h__4_132_);
lean_dec(v_h__3_131_);
v_pre_151_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_pre_151_);
v_i_152_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_i_152_);
lean_dec_ref(v_x_127_);
v_pre_153_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_pre_153_);
v_str_154_ = lean_ctor_get(v_x_128_, 1);
lean_inc_ref(v_str_154_);
lean_dec_ref(v_x_128_);
v___x_155_ = lean_apply_4(v_h__5_133_, v_pre_151_, v_i_152_, v_pre_153_, v_str_154_);
return v___x_155_;
}
default: 
{
lean_object* v_pre_156_; lean_object* v_i_157_; lean_object* v_pre_158_; lean_object* v_i_159_; lean_object* v___x_160_; 
lean_dec(v_h__5_133_);
lean_dec(v_h__3_131_);
v_pre_156_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_pre_156_);
v_i_157_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_i_157_);
lean_dec_ref(v_x_127_);
v_pre_158_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_pre_158_);
v_i_159_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_i_159_);
lean_dec_ref(v_x_128_);
v___x_160_ = lean_apply_4(v_h__4_132_, v_pre_156_, v_i_157_, v_pre_158_, v_i_159_);
return v___x_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (v_x_161_ == 1)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__2_163_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__1_162_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_162_);
v___x_166_ = lean_box(v_x_161_);
v___x_167_ = lean_apply_2(v_h__2_163_, v___x_166_, lean_box(0));
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
uint8_t v_x_17__boxed_171_; lean_object* v_res_172_; 
v_x_17__boxed_171_ = lean_unbox(v_x_168_);
v_res_172_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(v_x_17__boxed_171_, v_h__1_169_, v_h__2_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object* v_motive_173_, uint8_t v_x_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_){
_start:
{
if (v_x_174_ == 1)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_h__2_176_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_apply_1(v_h__1_175_, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_h__1_175_);
v___x_179_ = lean_box(v_x_174_);
v___x_180_ = lean_apply_2(v_h__2_176_, v___x_179_, lean_box(0));
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object* v_motive_181_, lean_object* v_x_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_){
_start:
{
uint8_t v_x_28__boxed_185_; lean_object* v_res_186_; 
v_x_28__boxed_185_ = lean_unbox(v_x_182_);
v_res_186_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(v_motive_181_, v_x_28__boxed_185_, v_h__1_183_, v_h__2_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object* v_ref_198_, lean_object* v_n_199_, uint8_t v_canonical_200_){
_start:
{
lean_object* v___x_201_; lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = l_Lean_SourceInfo_fromRef(v_ref_198_, v_canonical_200_);
v_ref_202_ = l_Lean_Syntax_setHeadInfo(v_ref_198_, v___x_201_);
v___x_203_ = lean_box(0);
lean_inc(v_n_199_);
v___x_204_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_203_, v_n_199_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; lean_object* v_stx_206_; 
v___x_205_ = l_Lean_quoteNameMk(v_n_199_);
v_stx_206_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_205_, v_ref_202_);
lean_dec(v_ref_202_);
return v_stx_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_stx_219_; 
lean_dec(v_n_199_);
v_val_207_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_207_);
lean_dec_ref(v___x_204_);
v___x_208_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__4));
v___x_209_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__5));
v___x_210_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__6));
v___x_211_ = lean_string_intercalate(v___x_210_, v_val_207_);
v___x_212_ = lean_string_append(v___x_209_, v___x_211_);
lean_dec_ref(v___x_211_);
v___x_213_ = lean_box(2);
v___x_214_ = l_Lean_Syntax_mkNameLit(v___x_212_, v___x_213_);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_mk_empty_array_with_capacity(v___x_215_);
v___x_217_ = lean_array_push(v___x_216_, v___x_214_);
v___x_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_218_, 0, v___x_213_);
lean_ctor_set(v___x_218_, 1, v___x_208_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
v_stx_219_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_218_, v_ref_202_);
lean_dec(v_ref_202_);
return v_stx_219_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object* v_ref_220_, lean_object* v_n_221_, lean_object* v_canonical_222_){
_start:
{
uint8_t v_canonical_boxed_223_; lean_object* v_res_224_; 
v_canonical_boxed_223_ = lean_unbox(v_canonical_222_);
v_res_224_ = l_Lake_Name_quoteFrom(v_ref_220_, v_n_221_, v_canonical_boxed_223_);
return v_res_224_;
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
