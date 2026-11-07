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
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_empty___redArg();
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
LEAN_EXPORT lean_object* l_Lake_NameMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_NameMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object*);
static const lean_closure_object l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg();
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object*);
static lean_once_cell_t l_Lake_OrdNameMap_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdNameMap_empty___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap___redArg();
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_NameMap_empty___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(1);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_NameMap_empty___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_NameMap_empty___redArg();
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object* v___y_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(1);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg(){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object* v_00_u03b1_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = ((lean_object*)(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0));
return v___x_18_;
}
}
static lean_object* _init_l_Lake_OrdNameMap_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lake_RBArray_empty___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty___redArg(){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty___redArg___boxed(lean_object* v___dummy_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lake_OrdNameMap_empty___redArg();
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object* v_00_u03b1_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_mkOrdNameMap___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object* v_00_u03b1_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty___redArg(){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(1);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty___redArg___boxed(lean_object* v___dummy_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lake_DNameMap_empty___redArg();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object* v_00_u03b1_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(1);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object* v_x_38_){
_start:
{
switch(lean_obj_tag(v_x_38_))
{
case 0:
{
return v_x_38_;
}
case 1:
{
lean_object* v_pre_39_; 
v_pre_39_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_pre_39_);
if (lean_obj_tag(v_pre_39_) == 0)
{
lean_dec_ref_known(v_x_38_, 2);
return v_pre_39_;
}
else
{
lean_object* v_str_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_str_40_ = lean_ctor_get(v_x_38_, 1);
lean_inc_ref(v_str_40_);
lean_dec_ref_known(v_x_38_, 2);
v___x_41_ = l_Lake_Name_eraseHead(v_pre_39_);
v___x_42_ = l_Lean_Name_str___override(v___x_41_, v_str_40_);
return v___x_42_;
}
}
default: 
{
lean_object* v_pre_43_; 
v_pre_43_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_pre_43_);
if (lean_obj_tag(v_pre_43_) == 0)
{
lean_dec_ref_known(v_x_38_, 2);
return v_pre_43_;
}
else
{
lean_object* v_i_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_i_44_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_i_44_);
lean_dec_ref_known(v_x_38_, 2);
v___x_45_ = l_Lake_Name_eraseHead(v_pre_43_);
v___x_46_ = l_Lean_Name_num___override(v___x_45_, v_i_44_);
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_49_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_h__1_48_, v___x_50_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
lean_dec(v_h__1_48_);
v___x_52_ = lean_apply_2(v_h__2_49_, v_x_47_, lean_box(0));
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_56_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__1_55_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; 
lean_dec(v_h__1_55_);
v___x_59_ = lean_apply_2(v_h__2_56_, v_x_54_, lean_box(0));
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_, lean_object* v_h__4_65_, lean_object* v_h__5_66_, lean_object* v_h__6_67_, lean_object* v_h__7_68_){
_start:
{
switch(lean_obj_tag(v_x_60_))
{
case 0:
{
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_63_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_62_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; 
lean_dec(v_h__1_62_);
v___x_71_ = lean_apply_2(v_h__2_63_, v_x_61_, lean_box(0));
return v___x_71_;
}
}
case 1:
{
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
switch(lean_obj_tag(v_x_61_))
{
case 0:
{
lean_object* v___x_72_; 
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
v___x_72_ = lean_apply_2(v_h__3_64_, v_x_60_, lean_box(0));
return v___x_72_;
}
case 1:
{
lean_object* v_pre_73_; lean_object* v_str_74_; lean_object* v_pre_75_; lean_object* v_str_76_; lean_object* v___x_77_; 
lean_dec(v_h__6_67_);
lean_dec(v_h__3_64_);
v_pre_73_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_pre_73_);
v_str_74_ = lean_ctor_get(v_x_60_, 1);
lean_inc_ref(v_str_74_);
lean_dec_ref_known(v_x_60_, 2);
v_pre_75_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_75_);
v_str_76_ = lean_ctor_get(v_x_61_, 1);
lean_inc_ref(v_str_76_);
lean_dec_ref_known(v_x_61_, 2);
v___x_77_ = lean_apply_4(v_h__7_68_, v_pre_73_, v_str_74_, v_pre_75_, v_str_76_);
return v___x_77_;
}
default: 
{
lean_object* v_pre_78_; lean_object* v_str_79_; lean_object* v_pre_80_; lean_object* v_i_81_; lean_object* v___x_82_; 
lean_dec(v_h__7_68_);
lean_dec(v_h__3_64_);
v_pre_78_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_pre_78_);
v_str_79_ = lean_ctor_get(v_x_60_, 1);
lean_inc_ref(v_str_79_);
lean_dec_ref_known(v_x_60_, 2);
v_pre_80_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_80_);
v_i_81_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_i_81_);
lean_dec_ref_known(v_x_61_, 2);
v___x_82_ = lean_apply_4(v_h__6_67_, v_pre_78_, v_str_79_, v_pre_80_, v_i_81_);
return v___x_82_;
}
}
}
default: 
{
lean_dec(v_h__7_68_);
lean_dec(v_h__6_67_);
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
switch(lean_obj_tag(v_x_61_))
{
case 0:
{
lean_object* v___x_83_; 
lean_dec(v_h__5_66_);
lean_dec(v_h__4_65_);
v___x_83_ = lean_apply_2(v_h__3_64_, v_x_60_, lean_box(0));
return v___x_83_;
}
case 1:
{
lean_object* v_pre_84_; lean_object* v_i_85_; lean_object* v_pre_86_; lean_object* v_str_87_; lean_object* v___x_88_; 
lean_dec(v_h__4_65_);
lean_dec(v_h__3_64_);
v_pre_84_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_pre_84_);
v_i_85_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_i_85_);
lean_dec_ref_known(v_x_60_, 2);
v_pre_86_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_86_);
v_str_87_ = lean_ctor_get(v_x_61_, 1);
lean_inc_ref(v_str_87_);
lean_dec_ref_known(v_x_61_, 2);
v___x_88_ = lean_apply_4(v_h__5_66_, v_pre_84_, v_i_85_, v_pre_86_, v_str_87_);
return v___x_88_;
}
default: 
{
lean_object* v_pre_89_; lean_object* v_i_90_; lean_object* v_pre_91_; lean_object* v_i_92_; lean_object* v___x_93_; 
lean_dec(v_h__5_66_);
lean_dec(v_h__3_64_);
v_pre_89_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_pre_89_);
v_i_90_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_i_90_);
lean_dec_ref_known(v_x_60_, 2);
v_pre_91_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_91_);
v_i_92_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_i_92_);
lean_dec_ref_known(v_x_61_, 2);
v___x_93_ = lean_apply_4(v_h__4_65_, v_pre_89_, v_i_90_, v_pre_91_, v_i_92_);
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object* v_motive_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_, lean_object* v_h__4_100_, lean_object* v_h__5_101_, lean_object* v_h__6_102_, lean_object* v_h__7_103_){
_start:
{
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
lean_dec(v_h__7_103_);
lean_dec(v_h__6_102_);
lean_dec(v_h__5_101_);
lean_dec(v_h__4_100_);
lean_dec(v_h__3_99_);
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_h__2_98_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v_h__1_97_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; 
lean_dec(v_h__1_97_);
v___x_106_ = lean_apply_2(v_h__2_98_, v_x_96_, lean_box(0));
return v___x_106_;
}
}
case 1:
{
lean_dec(v_h__5_101_);
lean_dec(v_h__4_100_);
lean_dec(v_h__2_98_);
lean_dec(v_h__1_97_);
switch(lean_obj_tag(v_x_96_))
{
case 0:
{
lean_object* v___x_107_; 
lean_dec(v_h__7_103_);
lean_dec(v_h__6_102_);
v___x_107_ = lean_apply_2(v_h__3_99_, v_x_95_, lean_box(0));
return v___x_107_;
}
case 1:
{
lean_object* v_pre_108_; lean_object* v_str_109_; lean_object* v_pre_110_; lean_object* v_str_111_; lean_object* v___x_112_; 
lean_dec(v_h__6_102_);
lean_dec(v_h__3_99_);
v_pre_108_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_pre_108_);
v_str_109_ = lean_ctor_get(v_x_95_, 1);
lean_inc_ref(v_str_109_);
lean_dec_ref_known(v_x_95_, 2);
v_pre_110_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_pre_110_);
v_str_111_ = lean_ctor_get(v_x_96_, 1);
lean_inc_ref(v_str_111_);
lean_dec_ref_known(v_x_96_, 2);
v___x_112_ = lean_apply_4(v_h__7_103_, v_pre_108_, v_str_109_, v_pre_110_, v_str_111_);
return v___x_112_;
}
default: 
{
lean_object* v_pre_113_; lean_object* v_str_114_; lean_object* v_pre_115_; lean_object* v_i_116_; lean_object* v___x_117_; 
lean_dec(v_h__7_103_);
lean_dec(v_h__3_99_);
v_pre_113_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_pre_113_);
v_str_114_ = lean_ctor_get(v_x_95_, 1);
lean_inc_ref(v_str_114_);
lean_dec_ref_known(v_x_95_, 2);
v_pre_115_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_pre_115_);
v_i_116_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_i_116_);
lean_dec_ref_known(v_x_96_, 2);
v___x_117_ = lean_apply_4(v_h__6_102_, v_pre_113_, v_str_114_, v_pre_115_, v_i_116_);
return v___x_117_;
}
}
}
default: 
{
lean_dec(v_h__7_103_);
lean_dec(v_h__6_102_);
lean_dec(v_h__2_98_);
lean_dec(v_h__1_97_);
switch(lean_obj_tag(v_x_96_))
{
case 0:
{
lean_object* v___x_118_; 
lean_dec(v_h__5_101_);
lean_dec(v_h__4_100_);
v___x_118_ = lean_apply_2(v_h__3_99_, v_x_95_, lean_box(0));
return v___x_118_;
}
case 1:
{
lean_object* v_pre_119_; lean_object* v_i_120_; lean_object* v_pre_121_; lean_object* v_str_122_; lean_object* v___x_123_; 
lean_dec(v_h__4_100_);
lean_dec(v_h__3_99_);
v_pre_119_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_pre_119_);
v_i_120_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_i_120_);
lean_dec_ref_known(v_x_95_, 2);
v_pre_121_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_pre_121_);
v_str_122_ = lean_ctor_get(v_x_96_, 1);
lean_inc_ref(v_str_122_);
lean_dec_ref_known(v_x_96_, 2);
v___x_123_ = lean_apply_4(v_h__5_101_, v_pre_119_, v_i_120_, v_pre_121_, v_str_122_);
return v___x_123_;
}
default: 
{
lean_object* v_pre_124_; lean_object* v_i_125_; lean_object* v_pre_126_; lean_object* v_i_127_; lean_object* v___x_128_; 
lean_dec(v_h__5_101_);
lean_dec(v_h__3_99_);
v_pre_124_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_pre_124_);
v_i_125_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_i_125_);
lean_dec_ref_known(v_x_95_, 2);
v_pre_126_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_pre_126_);
v_i_127_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_i_127_);
lean_dec_ref_known(v_x_96_, 2);
v___x_128_ = lean_apply_4(v_h__4_100_, v_pre_124_, v_i_125_, v_pre_126_, v_i_127_);
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (v_x_129_ == 1)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_131_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__1_130_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_h__1_130_);
v___x_134_ = lean_box(v_x_129_);
v___x_135_ = lean_apply_2(v_h__2_131_, v___x_134_, lean_box(0));
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_){
_start:
{
uint8_t v_x_13__boxed_139_; lean_object* v_res_140_; 
v_x_13__boxed_139_ = lean_unbox(v_x_136_);
v_res_140_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(v_x_13__boxed_139_, v_h__1_137_, v_h__2_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object* v_motive_141_, uint8_t v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (v_x_142_ == 1)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_144_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_1(v_h__1_143_, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v___x_147_ = lean_box(v_x_142_);
v___x_148_ = lean_apply_2(v_h__2_144_, v___x_147_, lean_box(0));
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
uint8_t v_x_24__boxed_153_; lean_object* v_res_154_; 
v_x_24__boxed_153_ = lean_unbox(v_x_150_);
v_res_154_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(v_motive_149_, v_x_24__boxed_153_, v_h__1_151_, v_h__2_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object* v_ref_166_, lean_object* v_n_167_, uint8_t v_canonical_168_){
_start:
{
lean_object* v___x_169_; lean_object* v_ref_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = l_Lean_SourceInfo_fromRef(v_ref_166_, v_canonical_168_);
v_ref_170_ = l_Lean_Syntax_setHeadInfo(v_ref_166_, v___x_169_);
v___x_171_ = lean_box(0);
lean_inc(v_n_167_);
v___x_172_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_171_, v_n_167_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v___x_173_; lean_object* v_stx_174_; 
v___x_173_ = l_Lean_quoteNameMk(v_n_167_);
v_stx_174_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_173_, v_ref_170_);
lean_dec(v_ref_170_);
return v_stx_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_stx_187_; 
lean_dec(v_n_167_);
v_val_175_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_172_, 1);
v___x_176_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__4));
v___x_177_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__5));
v___x_178_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__6));
v___x_179_ = lean_string_intercalate(v___x_178_, v_val_175_);
v___x_180_ = lean_string_append(v___x_177_, v___x_179_);
lean_dec_ref(v___x_179_);
v___x_181_ = lean_box(2);
v___x_182_ = l_Lean_Syntax_mkNameLit(v___x_180_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_183_);
v___x_185_ = lean_array_push(v___x_184_, v___x_182_);
v___x_186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_181_);
lean_ctor_set(v___x_186_, 1, v___x_176_);
lean_ctor_set(v___x_186_, 2, v___x_185_);
v_stx_187_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_186_, v_ref_170_);
lean_dec(v_ref_170_);
return v_stx_187_;
}
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
