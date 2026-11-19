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
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter___redArg(lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
switch(lean_obj_tag(v_x_61_))
{
case 0:
{
lean_object* v___x_65_; 
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
v___x_65_ = lean_apply_1(v_h__1_62_, v_x_60_);
return v___x_65_;
}
case 1:
{
lean_object* v_pre_66_; lean_object* v_str_67_; lean_object* v___x_68_; 
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v_pre_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_66_);
v_str_67_ = lean_ctor_get(v_x_61_, 1);
lean_inc_ref(v_str_67_);
lean_dec_ref_known(v_x_61_, 2);
v___x_68_ = lean_apply_3(v_h__3_64_, v_x_60_, v_pre_66_, v_str_67_);
return v___x_68_;
}
default: 
{
lean_object* v_pre_69_; lean_object* v_i_70_; lean_object* v___x_71_; 
lean_dec(v_h__3_64_);
lean_dec(v_h__1_62_);
v_pre_69_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_69_);
v_i_70_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_i_70_);
lean_dec_ref_known(v_x_61_, 2);
v___x_71_ = lean_apply_3(v_h__2_63_, v_x_60_, v_pre_69_, v_i_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter(lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_){
_start:
{
switch(lean_obj_tag(v_x_74_))
{
case 0:
{
lean_object* v___x_78_; 
lean_dec(v_h__3_77_);
lean_dec(v_h__2_76_);
v___x_78_ = lean_apply_1(v_h__1_75_, v_x_73_);
return v___x_78_;
}
case 1:
{
lean_object* v_pre_79_; lean_object* v_str_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_76_);
lean_dec(v_h__1_75_);
v_pre_79_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_pre_79_);
v_str_80_ = lean_ctor_get(v_x_74_, 1);
lean_inc_ref(v_str_80_);
lean_dec_ref_known(v_x_74_, 2);
v___x_81_ = lean_apply_3(v_h__3_77_, v_x_73_, v_pre_79_, v_str_80_);
return v___x_81_;
}
default: 
{
lean_object* v_pre_82_; lean_object* v_i_83_; lean_object* v___x_84_; 
lean_dec(v_h__3_77_);
lean_dec(v_h__1_75_);
v_pre_82_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_pre_82_);
v_i_83_ = lean_ctor_get(v_x_74_, 1);
lean_inc(v_i_83_);
lean_dec_ref_known(v_x_74_, 2);
v___x_84_ = lean_apply_3(v_h__2_76_, v_x_73_, v_pre_82_, v_i_83_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_, lean_object* v_h__3_89_){
_start:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
lean_object* v___x_90_; 
lean_dec(v_h__3_89_);
lean_dec(v_h__2_88_);
v___x_90_ = lean_apply_1(v_h__1_87_, v_x_85_);
return v___x_90_;
}
case 1:
{
lean_object* v_pre_91_; lean_object* v_str_92_; lean_object* v___x_93_; 
lean_dec(v_h__3_89_);
lean_dec(v_h__1_87_);
v_pre_91_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_pre_91_);
v_str_92_ = lean_ctor_get(v_x_86_, 1);
lean_inc_ref(v_str_92_);
lean_dec_ref_known(v_x_86_, 2);
v___x_93_ = lean_apply_3(v_h__2_88_, v_x_85_, v_pre_91_, v_str_92_);
return v___x_93_;
}
default: 
{
lean_object* v_pre_94_; lean_object* v_i_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_88_);
lean_dec(v_h__1_87_);
v_pre_94_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_pre_94_);
v_i_95_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_i_95_);
lean_dec_ref_known(v_x_86_, 2);
v___x_96_ = lean_apply_3(v_h__3_89_, v_x_85_, v_pre_94_, v_i_95_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter(lean_object* v_motive_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_, lean_object* v_h__3_102_){
_start:
{
switch(lean_obj_tag(v_x_99_))
{
case 0:
{
lean_object* v___x_103_; 
lean_dec(v_h__3_102_);
lean_dec(v_h__2_101_);
v___x_103_ = lean_apply_1(v_h__1_100_, v_x_98_);
return v___x_103_;
}
case 1:
{
lean_object* v_pre_104_; lean_object* v_str_105_; lean_object* v___x_106_; 
lean_dec(v_h__3_102_);
lean_dec(v_h__1_100_);
v_pre_104_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_pre_104_);
v_str_105_ = lean_ctor_get(v_x_99_, 1);
lean_inc_ref(v_str_105_);
lean_dec_ref_known(v_x_99_, 2);
v___x_106_ = lean_apply_3(v_h__2_101_, v_x_98_, v_pre_104_, v_str_105_);
return v___x_106_;
}
default: 
{
lean_object* v_pre_107_; lean_object* v_i_108_; lean_object* v___x_109_; 
lean_dec(v_h__2_101_);
lean_dec(v_h__1_100_);
v_pre_107_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_pre_107_);
v_i_108_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_i_108_);
lean_dec_ref_known(v_x_99_, 2);
v___x_109_ = lean_apply_3(v_h__3_102_, v_x_98_, v_pre_107_, v_i_108_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_, lean_object* v_h__4_115_, lean_object* v_h__5_116_, lean_object* v_h__6_117_, lean_object* v_h__7_118_){
_start:
{
switch(lean_obj_tag(v_x_110_))
{
case 0:
{
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
if (lean_obj_tag(v_x_111_) == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_113_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_apply_1(v_h__1_112_, v___x_119_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_h__1_112_);
v___x_121_ = lean_apply_2(v_h__2_113_, v_x_111_, lean_box(0));
return v___x_121_;
}
}
case 1:
{
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
lean_object* v___x_122_; 
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
v___x_122_ = lean_apply_2(v_h__3_114_, v_x_110_, lean_box(0));
return v___x_122_;
}
case 1:
{
lean_object* v_pre_123_; lean_object* v_str_124_; lean_object* v_pre_125_; lean_object* v_str_126_; lean_object* v___x_127_; 
lean_dec(v_h__6_117_);
lean_dec(v_h__3_114_);
v_pre_123_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_pre_123_);
v_str_124_ = lean_ctor_get(v_x_110_, 1);
lean_inc_ref(v_str_124_);
lean_dec_ref_known(v_x_110_, 2);
v_pre_125_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_pre_125_);
v_str_126_ = lean_ctor_get(v_x_111_, 1);
lean_inc_ref(v_str_126_);
lean_dec_ref_known(v_x_111_, 2);
v___x_127_ = lean_apply_4(v_h__7_118_, v_pre_123_, v_str_124_, v_pre_125_, v_str_126_);
return v___x_127_;
}
default: 
{
lean_object* v_pre_128_; lean_object* v_str_129_; lean_object* v_pre_130_; lean_object* v_i_131_; lean_object* v___x_132_; 
lean_dec(v_h__7_118_);
lean_dec(v_h__3_114_);
v_pre_128_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_pre_128_);
v_str_129_ = lean_ctor_get(v_x_110_, 1);
lean_inc_ref(v_str_129_);
lean_dec_ref_known(v_x_110_, 2);
v_pre_130_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_pre_130_);
v_i_131_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_i_131_);
lean_dec_ref_known(v_x_111_, 2);
v___x_132_ = lean_apply_4(v_h__6_117_, v_pre_128_, v_str_129_, v_pre_130_, v_i_131_);
return v___x_132_;
}
}
}
default: 
{
lean_dec(v_h__7_118_);
lean_dec(v_h__6_117_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
lean_object* v___x_133_; 
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
v___x_133_ = lean_apply_2(v_h__3_114_, v_x_110_, lean_box(0));
return v___x_133_;
}
case 1:
{
lean_object* v_pre_134_; lean_object* v_i_135_; lean_object* v_pre_136_; lean_object* v_str_137_; lean_object* v___x_138_; 
lean_dec(v_h__4_115_);
lean_dec(v_h__3_114_);
v_pre_134_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_pre_134_);
v_i_135_ = lean_ctor_get(v_x_110_, 1);
lean_inc(v_i_135_);
lean_dec_ref_known(v_x_110_, 2);
v_pre_136_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_pre_136_);
v_str_137_ = lean_ctor_get(v_x_111_, 1);
lean_inc_ref(v_str_137_);
lean_dec_ref_known(v_x_111_, 2);
v___x_138_ = lean_apply_4(v_h__5_116_, v_pre_134_, v_i_135_, v_pre_136_, v_str_137_);
return v___x_138_;
}
default: 
{
lean_object* v_pre_139_; lean_object* v_i_140_; lean_object* v_pre_141_; lean_object* v_i_142_; lean_object* v___x_143_; 
lean_dec(v_h__5_116_);
lean_dec(v_h__3_114_);
v_pre_139_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_pre_139_);
v_i_140_ = lean_ctor_get(v_x_110_, 1);
lean_inc(v_i_140_);
lean_dec_ref_known(v_x_110_, 2);
v_pre_141_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_pre_141_);
v_i_142_ = lean_ctor_get(v_x_111_, 1);
lean_inc(v_i_142_);
lean_dec_ref_known(v_x_111_, 2);
v___x_143_ = lean_apply_4(v_h__4_115_, v_pre_139_, v_i_140_, v_pre_141_, v_i_142_);
return v___x_143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_, lean_object* v_h__3_149_, lean_object* v_h__4_150_, lean_object* v_h__5_151_, lean_object* v_h__6_152_, lean_object* v_h__7_153_){
_start:
{
switch(lean_obj_tag(v_x_145_))
{
case 0:
{
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_148_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_apply_1(v_h__1_147_, v___x_154_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
lean_dec(v_h__1_147_);
v___x_156_ = lean_apply_2(v_h__2_148_, v_x_146_, lean_box(0));
return v___x_156_;
}
}
case 1:
{
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
switch(lean_obj_tag(v_x_146_))
{
case 0:
{
lean_object* v___x_157_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
v___x_157_ = lean_apply_2(v_h__3_149_, v_x_145_, lean_box(0));
return v___x_157_;
}
case 1:
{
lean_object* v_pre_158_; lean_object* v_str_159_; lean_object* v_pre_160_; lean_object* v_str_161_; lean_object* v___x_162_; 
lean_dec(v_h__6_152_);
lean_dec(v_h__3_149_);
v_pre_158_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_pre_158_);
v_str_159_ = lean_ctor_get(v_x_145_, 1);
lean_inc_ref(v_str_159_);
lean_dec_ref_known(v_x_145_, 2);
v_pre_160_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_pre_160_);
v_str_161_ = lean_ctor_get(v_x_146_, 1);
lean_inc_ref(v_str_161_);
lean_dec_ref_known(v_x_146_, 2);
v___x_162_ = lean_apply_4(v_h__7_153_, v_pre_158_, v_str_159_, v_pre_160_, v_str_161_);
return v___x_162_;
}
default: 
{
lean_object* v_pre_163_; lean_object* v_str_164_; lean_object* v_pre_165_; lean_object* v_i_166_; lean_object* v___x_167_; 
lean_dec(v_h__7_153_);
lean_dec(v_h__3_149_);
v_pre_163_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_pre_163_);
v_str_164_ = lean_ctor_get(v_x_145_, 1);
lean_inc_ref(v_str_164_);
lean_dec_ref_known(v_x_145_, 2);
v_pre_165_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_pre_165_);
v_i_166_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_i_166_);
lean_dec_ref_known(v_x_146_, 2);
v___x_167_ = lean_apply_4(v_h__6_152_, v_pre_163_, v_str_164_, v_pre_165_, v_i_166_);
return v___x_167_;
}
}
}
default: 
{
lean_dec(v_h__7_153_);
lean_dec(v_h__6_152_);
lean_dec(v_h__2_148_);
lean_dec(v_h__1_147_);
switch(lean_obj_tag(v_x_146_))
{
case 0:
{
lean_object* v___x_168_; 
lean_dec(v_h__5_151_);
lean_dec(v_h__4_150_);
v___x_168_ = lean_apply_2(v_h__3_149_, v_x_145_, lean_box(0));
return v___x_168_;
}
case 1:
{
lean_object* v_pre_169_; lean_object* v_i_170_; lean_object* v_pre_171_; lean_object* v_str_172_; lean_object* v___x_173_; 
lean_dec(v_h__4_150_);
lean_dec(v_h__3_149_);
v_pre_169_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_pre_169_);
v_i_170_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_i_170_);
lean_dec_ref_known(v_x_145_, 2);
v_pre_171_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_pre_171_);
v_str_172_ = lean_ctor_get(v_x_146_, 1);
lean_inc_ref(v_str_172_);
lean_dec_ref_known(v_x_146_, 2);
v___x_173_ = lean_apply_4(v_h__5_151_, v_pre_169_, v_i_170_, v_pre_171_, v_str_172_);
return v___x_173_;
}
default: 
{
lean_object* v_pre_174_; lean_object* v_i_175_; lean_object* v_pre_176_; lean_object* v_i_177_; lean_object* v___x_178_; 
lean_dec(v_h__5_151_);
lean_dec(v_h__3_149_);
v_pre_174_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_pre_174_);
v_i_175_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_i_175_);
lean_dec_ref_known(v_x_145_, 2);
v_pre_176_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_pre_176_);
v_i_177_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_i_177_);
lean_dec_ref_known(v_x_146_, 2);
v___x_178_ = lean_apply_4(v_h__4_150_, v_pre_174_, v_i_175_, v_pre_176_, v_i_177_);
return v___x_178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t v_x_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
if (v_x_179_ == 1)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_181_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_apply_1(v_h__1_180_, v___x_182_);
return v___x_183_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_h__1_180_);
v___x_184_ = lean_box(v_x_179_);
v___x_185_ = lean_apply_2(v_h__2_181_, v___x_184_, lean_box(0));
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
uint8_t v_x_13__boxed_189_; lean_object* v_res_190_; 
v_x_13__boxed_189_ = lean_unbox(v_x_186_);
v_res_190_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(v_x_13__boxed_189_, v_h__1_187_, v_h__2_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object* v_motive_191_, uint8_t v_x_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
if (v_x_192_ == 1)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_h__2_194_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_1(v_h__1_193_, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_193_);
v___x_197_ = lean_box(v_x_192_);
v___x_198_ = lean_apply_2(v_h__2_194_, v___x_197_, lean_box(0));
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object* v_motive_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
uint8_t v_x_24__boxed_203_; lean_object* v_res_204_; 
v_x_24__boxed_203_ = lean_unbox(v_x_200_);
v_res_204_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(v_motive_199_, v_x_24__boxed_203_, v_h__1_201_, v_h__2_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object* v_ref_216_, lean_object* v_n_217_, uint8_t v_canonical_218_){
_start:
{
lean_object* v___x_219_; lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_219_ = l_Lean_SourceInfo_fromRef(v_ref_216_, v_canonical_218_);
v_ref_220_ = l_Lean_Syntax_setHeadInfo(v_ref_216_, v___x_219_);
v___x_221_ = lean_box(0);
lean_inc(v_n_217_);
v___x_222_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_221_, v_n_217_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; lean_object* v_stx_224_; 
v___x_223_ = l_Lean_quoteNameMk(v_n_217_);
v_stx_224_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_223_, v_ref_220_);
lean_dec(v_ref_220_);
return v_stx_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_stx_237_; 
lean_dec(v_n_217_);
v_val_225_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_222_, 1);
v___x_226_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__4));
v___x_227_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__5));
v___x_228_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__6));
v___x_229_ = lean_string_intercalate(v___x_228_, v_val_225_);
v___x_230_ = lean_string_append(v___x_227_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = lean_box(2);
v___x_232_ = l_Lean_Syntax_mkNameLit(v___x_230_, v___x_231_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_array_push(v___x_234_, v___x_232_);
v___x_236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_231_);
lean_ctor_set(v___x_236_, 1, v___x_226_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
v_stx_237_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_236_, v_ref_220_);
lean_dec(v_ref_220_);
return v_stx_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object* v_ref_238_, lean_object* v_n_239_, lean_object* v_canonical_240_){
_start:
{
uint8_t v_canonical_boxed_241_; lean_object* v_res_242_; 
v_canonical_boxed_241_ = lean_unbox(v_canonical_240_);
v_res_242_ = l_Lake_Name_quoteFrom(v_ref_238_, v_n_239_, v_canonical_boxed_241_);
return v_res_242_;
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
