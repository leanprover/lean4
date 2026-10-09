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
lean_object* l_Lake_NameMap_empty___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(1);
return v___x_7_;
}
}
LEAN_EXPORT void l_Lake_NameMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_8_;
v_res_8_ = l_Lake_NameMap_empty___redArg();
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_NameMap_empty___redArg___boxed(lean_object* v___dummy_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_NameMap_empty___redArg();
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object* v___y_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(1);
return v___x_12_;
}
}
lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0));
return v___x_15_;
}
}
LEAN_EXPORT void l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object* v_00_u03b1_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = ((lean_object*)(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___redArg___closed__0));
return v___x_20_;
}
}
static lean_object* _init_l_Lake_OrdNameMap_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_RBArray_empty___redArg();
return v___x_21_;
}
}
lean_object* l_Lake_OrdNameMap_empty___redArg(){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_23_;
}
}
LEAN_EXPORT void l_Lake_OrdNameMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_24_;
v_res_24_ = l_Lake_OrdNameMap_empty___redArg();
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty___redArg___boxed(lean_object* v___dummy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_OrdNameMap_empty___redArg();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object* v_00_u03b1_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_28_;
}
}
lean_object* l_Lake_mkOrdNameMap___redArg(){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lake_mkOrdNameMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_31_;
v_res_31_ = l_Lake_mkOrdNameMap___redArg();
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap___redArg___boxed(lean_object* v___dummy_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lake_mkOrdNameMap___redArg();
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object* v_00_u03b1_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l_Lake_OrdNameMap_empty___redArg___closed__0, &l_Lake_OrdNameMap_empty___redArg___closed__0_once, _init_l_Lake_OrdNameMap_empty___redArg___closed__0);
return v___x_35_;
}
}
lean_object* l_Lake_DNameMap_empty___redArg(){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(1);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lake_DNameMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_38_;
v_res_38_ = l_Lake_DNameMap_empty___redArg();
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_DNameMap_empty___redArg();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object* v_00_u03b1_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(1);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object* v_x_43_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
return v_x_43_;
}
case 1:
{
lean_object* v_pre_44_; 
v_pre_44_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_pre_44_);
if (lean_obj_tag(v_pre_44_) == 0)
{
lean_dec_ref_known(v_x_43_, 2);
return v_pre_44_;
}
else
{
lean_object* v_str_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_str_45_ = lean_ctor_get(v_x_43_, 1);
lean_inc_ref(v_str_45_);
lean_dec_ref_known(v_x_43_, 2);
v___x_46_ = l_Lake_Name_eraseHead(v_pre_44_);
v___x_47_ = l_Lean_Name_str___override(v___x_46_, v_str_45_);
return v___x_47_;
}
}
default: 
{
lean_object* v_pre_48_; 
v_pre_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_pre_48_);
if (lean_obj_tag(v_pre_48_) == 0)
{
lean_dec_ref_known(v_x_43_, 2);
return v_pre_48_;
}
else
{
lean_object* v_i_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_i_49_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_i_49_);
lean_dec_ref_known(v_x_43_, 2);
v___x_50_ = l_Lake_Name_eraseHead(v_pre_48_);
v___x_51_ = l_Lean_Name_num___override(v___x_50_, v_i_49_);
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__1_53_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
lean_dec(v_h__1_53_);
v___x_57_ = lean_apply_2(v_h__2_54_, v_x_52_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_61_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__1_60_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
lean_dec(v_h__1_60_);
v___x_64_ = lean_apply_2(v_h__2_61_, v_x_59_, lean_box(0));
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_, lean_object* v_h__3_69_, lean_object* v_h__4_70_, lean_object* v_h__5_71_, lean_object* v_h__6_72_, lean_object* v_h__7_73_){
_start:
{
switch(lean_obj_tag(v_x_65_))
{
case 0:
{
lean_dec(v_h__7_73_);
lean_dec(v_h__6_72_);
lean_dec(v_h__5_71_);
lean_dec(v_h__4_70_);
lean_dec(v_h__3_69_);
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__2_68_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__1_67_, v___x_74_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
lean_dec(v_h__1_67_);
v___x_76_ = lean_apply_2(v_h__2_68_, v_x_66_, lean_box(0));
return v___x_76_;
}
}
case 1:
{
lean_dec(v_h__5_71_);
lean_dec(v_h__4_70_);
lean_dec(v_h__2_68_);
lean_dec(v_h__1_67_);
switch(lean_obj_tag(v_x_66_))
{
case 0:
{
lean_object* v___x_77_; 
lean_dec(v_h__7_73_);
lean_dec(v_h__6_72_);
v___x_77_ = lean_apply_2(v_h__3_69_, v_x_65_, lean_box(0));
return v___x_77_;
}
case 1:
{
lean_object* v_pre_78_; lean_object* v_str_79_; lean_object* v_pre_80_; lean_object* v_str_81_; lean_object* v___x_82_; 
lean_dec(v_h__6_72_);
lean_dec(v_h__3_69_);
v_pre_78_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_pre_78_);
v_str_79_ = lean_ctor_get(v_x_65_, 1);
lean_inc_ref(v_str_79_);
lean_dec_ref_known(v_x_65_, 2);
v_pre_80_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_pre_80_);
v_str_81_ = lean_ctor_get(v_x_66_, 1);
lean_inc_ref(v_str_81_);
lean_dec_ref_known(v_x_66_, 2);
v___x_82_ = lean_apply_4(v_h__7_73_, v_pre_78_, v_str_79_, v_pre_80_, v_str_81_);
return v___x_82_;
}
default: 
{
lean_object* v_pre_83_; lean_object* v_str_84_; lean_object* v_pre_85_; lean_object* v_i_86_; lean_object* v___x_87_; 
lean_dec(v_h__7_73_);
lean_dec(v_h__3_69_);
v_pre_83_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_pre_83_);
v_str_84_ = lean_ctor_get(v_x_65_, 1);
lean_inc_ref(v_str_84_);
lean_dec_ref_known(v_x_65_, 2);
v_pre_85_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_pre_85_);
v_i_86_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_i_86_);
lean_dec_ref_known(v_x_66_, 2);
v___x_87_ = lean_apply_4(v_h__6_72_, v_pre_83_, v_str_84_, v_pre_85_, v_i_86_);
return v___x_87_;
}
}
}
default: 
{
lean_dec(v_h__7_73_);
lean_dec(v_h__6_72_);
lean_dec(v_h__2_68_);
lean_dec(v_h__1_67_);
switch(lean_obj_tag(v_x_66_))
{
case 0:
{
lean_object* v___x_88_; 
lean_dec(v_h__5_71_);
lean_dec(v_h__4_70_);
v___x_88_ = lean_apply_2(v_h__3_69_, v_x_65_, lean_box(0));
return v___x_88_;
}
case 1:
{
lean_object* v_pre_89_; lean_object* v_i_90_; lean_object* v_pre_91_; lean_object* v_str_92_; lean_object* v___x_93_; 
lean_dec(v_h__4_70_);
lean_dec(v_h__3_69_);
v_pre_89_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_pre_89_);
v_i_90_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_i_90_);
lean_dec_ref_known(v_x_65_, 2);
v_pre_91_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_pre_91_);
v_str_92_ = lean_ctor_get(v_x_66_, 1);
lean_inc_ref(v_str_92_);
lean_dec_ref_known(v_x_66_, 2);
v___x_93_ = lean_apply_4(v_h__5_71_, v_pre_89_, v_i_90_, v_pre_91_, v_str_92_);
return v___x_93_;
}
default: 
{
lean_object* v_pre_94_; lean_object* v_i_95_; lean_object* v_pre_96_; lean_object* v_i_97_; lean_object* v___x_98_; 
lean_dec(v_h__5_71_);
lean_dec(v_h__3_69_);
v_pre_94_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_pre_94_);
v_i_95_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_i_95_);
lean_dec_ref_known(v_x_65_, 2);
v_pre_96_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_pre_96_);
v_i_97_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_i_97_);
lean_dec_ref_known(v_x_66_, 2);
v___x_98_ = lean_apply_4(v_h__4_70_, v_pre_94_, v_i_95_, v_pre_96_, v_i_97_);
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_, lean_object* v_h__3_104_, lean_object* v_h__4_105_, lean_object* v_h__5_106_, lean_object* v_h__6_107_, lean_object* v_h__7_108_){
_start:
{
switch(lean_obj_tag(v_x_100_))
{
case 0:
{
lean_dec(v_h__7_108_);
lean_dec(v_h__6_107_);
lean_dec(v_h__5_106_);
lean_dec(v_h__4_105_);
lean_dec(v_h__3_104_);
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_103_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__1_102_, v___x_109_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; 
lean_dec(v_h__1_102_);
v___x_111_ = lean_apply_2(v_h__2_103_, v_x_101_, lean_box(0));
return v___x_111_;
}
}
case 1:
{
lean_dec(v_h__5_106_);
lean_dec(v_h__4_105_);
lean_dec(v_h__2_103_);
lean_dec(v_h__1_102_);
switch(lean_obj_tag(v_x_101_))
{
case 0:
{
lean_object* v___x_112_; 
lean_dec(v_h__7_108_);
lean_dec(v_h__6_107_);
v___x_112_ = lean_apply_2(v_h__3_104_, v_x_100_, lean_box(0));
return v___x_112_;
}
case 1:
{
lean_object* v_pre_113_; lean_object* v_str_114_; lean_object* v_pre_115_; lean_object* v_str_116_; lean_object* v___x_117_; 
lean_dec(v_h__6_107_);
lean_dec(v_h__3_104_);
v_pre_113_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_pre_113_);
v_str_114_ = lean_ctor_get(v_x_100_, 1);
lean_inc_ref(v_str_114_);
lean_dec_ref_known(v_x_100_, 2);
v_pre_115_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_pre_115_);
v_str_116_ = lean_ctor_get(v_x_101_, 1);
lean_inc_ref(v_str_116_);
lean_dec_ref_known(v_x_101_, 2);
v___x_117_ = lean_apply_4(v_h__7_108_, v_pre_113_, v_str_114_, v_pre_115_, v_str_116_);
return v___x_117_;
}
default: 
{
lean_object* v_pre_118_; lean_object* v_str_119_; lean_object* v_pre_120_; lean_object* v_i_121_; lean_object* v___x_122_; 
lean_dec(v_h__7_108_);
lean_dec(v_h__3_104_);
v_pre_118_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_pre_118_);
v_str_119_ = lean_ctor_get(v_x_100_, 1);
lean_inc_ref(v_str_119_);
lean_dec_ref_known(v_x_100_, 2);
v_pre_120_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_pre_120_);
v_i_121_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_i_121_);
lean_dec_ref_known(v_x_101_, 2);
v___x_122_ = lean_apply_4(v_h__6_107_, v_pre_118_, v_str_119_, v_pre_120_, v_i_121_);
return v___x_122_;
}
}
}
default: 
{
lean_dec(v_h__7_108_);
lean_dec(v_h__6_107_);
lean_dec(v_h__2_103_);
lean_dec(v_h__1_102_);
switch(lean_obj_tag(v_x_101_))
{
case 0:
{
lean_object* v___x_123_; 
lean_dec(v_h__5_106_);
lean_dec(v_h__4_105_);
v___x_123_ = lean_apply_2(v_h__3_104_, v_x_100_, lean_box(0));
return v___x_123_;
}
case 1:
{
lean_object* v_pre_124_; lean_object* v_i_125_; lean_object* v_pre_126_; lean_object* v_str_127_; lean_object* v___x_128_; 
lean_dec(v_h__4_105_);
lean_dec(v_h__3_104_);
v_pre_124_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_pre_124_);
v_i_125_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_i_125_);
lean_dec_ref_known(v_x_100_, 2);
v_pre_126_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_pre_126_);
v_str_127_ = lean_ctor_get(v_x_101_, 1);
lean_inc_ref(v_str_127_);
lean_dec_ref_known(v_x_101_, 2);
v___x_128_ = lean_apply_4(v_h__5_106_, v_pre_124_, v_i_125_, v_pre_126_, v_str_127_);
return v___x_128_;
}
default: 
{
lean_object* v_pre_129_; lean_object* v_i_130_; lean_object* v_pre_131_; lean_object* v_i_132_; lean_object* v___x_133_; 
lean_dec(v_h__5_106_);
lean_dec(v_h__3_104_);
v_pre_129_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_pre_129_);
v_i_130_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_i_130_);
lean_dec_ref_known(v_x_100_, 2);
v_pre_131_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_pre_131_);
v_i_132_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_i_132_);
lean_dec_ref_known(v_x_101_, 2);
v___x_133_ = lean_apply_4(v_h__4_105_, v_pre_129_, v_i_130_, v_pre_131_, v_i_132_);
return v___x_133_;
}
}
}
}
}
}
lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
if (v_x_134_ == 1)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_136_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__1_135_, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_h__1_135_);
v___x_139_ = lean_box(v_x_134_);
v___x_140_ = lean_apply_2(v_h__2_136_, v___x_139_, lean_box(0));
return v___x_140_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_134_ = stack[0].m_num;
lean_object* v_h__1_135_ = stack[1].m_obj;
lean_object* v_h__2_136_ = stack[2].m_obj;
lean_object* v_res_141_;
v_res_141_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(v_x_134_, v_h__1_135_, v_h__2_136_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
uint8_t v_x_13__boxed_145_; lean_object* v_res_146_; 
v_x_13__boxed_145_ = lean_unbox(v_x_142_);
v_res_146_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(v_x_13__boxed_145_, v_h__1_143_, v_h__2_144_);
return v_res_146_;
}
}
lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object* v_motive_147_, uint8_t v_x_148_, lean_object* v_h__1_149_, lean_object* v_h__2_150_){
_start:
{
if (v_x_148_ == 1)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_h__2_150_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v_h__1_149_, v___x_151_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_h__1_149_);
v___x_153_ = lean_box(v_x_148_);
v___x_154_ = lean_apply_2(v_h__2_150_, v___x_153_, lean_box(0));
return v___x_154_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_148_ = stack[1].m_num;
lean_object* v_h__1_149_ = stack[2].m_obj;
lean_object* v_h__2_150_ = stack[3].m_obj;
lean_object* v_res_155_;
v_res_155_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_box(0), v_x_148_, v_h__1_149_, v_h__2_150_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
uint8_t v_x_30__boxed_160_; lean_object* v_res_161_; 
v_x_30__boxed_160_ = lean_unbox(v_x_157_);
v_res_161_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(v_motive_156_, v_x_30__boxed_160_, v_h__1_158_, v_h__2_159_);
return v_res_161_;
}
}
lean_object* l_Lake_Name_quoteFrom(lean_object* v_ref_173_, lean_object* v_n_174_, uint8_t v_canonical_175_){
_start:
{
lean_object* v___x_176_; lean_object* v_ref_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = l_Lean_SourceInfo_fromRef(v_ref_173_, v_canonical_175_);
v_ref_177_ = l_Lean_Syntax_setHeadInfo(v_ref_173_, v___x_176_);
v___x_178_ = lean_box(0);
lean_inc(v_n_174_);
v___x_179_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_178_, v_n_174_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v___x_180_; lean_object* v_stx_181_; 
v___x_180_ = l_Lean_quoteNameMk(v_n_174_);
v_stx_181_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_180_, v_ref_177_);
lean_dec(v_ref_177_);
return v_stx_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_stx_194_; 
lean_dec(v_n_174_);
v_val_182_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v___x_179_, 1);
v___x_183_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__4));
v___x_184_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__5));
v___x_185_ = ((lean_object*)(l_Lake_Name_quoteFrom___closed__6));
v___x_186_ = lean_string_intercalate(v___x_185_, v_val_182_);
v___x_187_ = lean_string_append(v___x_184_, v___x_186_);
lean_dec_ref(v___x_186_);
v___x_188_ = lean_box(2);
v___x_189_ = l_Lean_Syntax_mkNameLit(v___x_187_, v___x_188_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_mk_empty_array_with_capacity(v___x_190_);
v___x_192_ = lean_array_push(v___x_191_, v___x_189_);
v___x_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_188_);
lean_ctor_set(v___x_193_, 1, v___x_183_);
lean_ctor_set(v___x_193_, 2, v___x_192_);
v_stx_194_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_193_, v_ref_177_);
lean_dec(v_ref_177_);
return v_stx_194_;
}
}
}
LEAN_EXPORT void l_Lake_Name_quoteFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_173_ = stack[0].m_obj;
lean_object* v_n_174_ = stack[1].m_obj;
uint8_t v_canonical_175_ = stack[2].m_num;
lean_object* v_res_195_;
v_res_195_ = l_Lake_Name_quoteFrom(v_ref_173_, v_n_174_, v_canonical_175_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object* v_ref_196_, lean_object* v_n_197_, lean_object* v_canonical_198_){
_start:
{
uint8_t v_canonical_boxed_199_; lean_object* v_res_200_; 
v_canonical_boxed_199_ = lean_unbox(v_canonical_198_);
v_res_200_ = l_Lake_Name_quoteFrom(v_ref_196_, v_n_197_, v_canonical_boxed_199_);
return v_res_200_;
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
