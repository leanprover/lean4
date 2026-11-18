// Lean compiler output
// Module: Lean.Linter.CodeQuality.Basic
// Imports: public import Init.Data.Float public import Std.Data.TreeMap.Basic public import Init.Data.Ord public import Lean.Data.Json
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
lean_object* l_Lean_Float_toJson(double);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0_value;
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1_value;
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__2 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson(lean_object*);
static const lean_closure_object l_Lean_Linter_CodeQuality_instToJsonSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_CodeQuality_instToJsonSource_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonSource___closed__0 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_CodeQuality_instToJsonSource = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonSource___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scalar"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__0 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__0_value;
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1_value;
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dict"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__2 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__2_value;
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dictionary"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__3 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson(lean_object*);
static const lean_closure_object l_Lean_Linter_CodeQuality_instToJsonValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_CodeQuality_instToJsonValue_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonValue___closed__0 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_CodeQuality_instToJsonValue = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__0 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__0_value;
static const lean_array_object l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__1 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(lean_object*);
static const lean_closure_object l_Lean_Linter_CodeQuality_instToJsonEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_CodeQuality_instToJsonEntry_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry___closed__0 = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry = (const lean_object*)&l_Lean_Linter_CodeQuality_instToJsonEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Linter_CodeQuality_Source_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_name_7_; lean_object* v___x_8_; 
v_name_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_name_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_name_7_);
return v___x_8_;
}
else
{
lean_object* v_module_9_; lean_object* v_name_10_; lean_object* v___x_11_; 
v_module_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_module_9_);
v_name_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_name_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_module_9_, v_name_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Linter_CodeQuality_Source_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim___redArg(lean_object* v_t_24_, lean_object* v_module_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_24_, v_module_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_module_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_28_, v_module_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim___redArg(lean_object* v_t_32_, lean_object* v_declaration_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_32_, v_declaration_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_declaration_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_36_, v_declaration_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson(lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_name_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_62_; 
v_name_44_ = lean_ctor_get(v_x_43_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_62_ == 0)
{
v___x_46_ = v_x_43_;
v_isShared_47_ = v_isSharedCheck_62_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_name_44_);
lean_dec(v_x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_62_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_48_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0));
v___x_49_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_50_ = 1;
v___x_51_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_44_, v___x_50_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 3);
lean_ctor_set(v___x_46_, 0, v___x_51_);
v___x_53_ = v___x_46_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_61_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_49_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = l_Lean_Json_mkObj(v___x_56_);
lean_dec_ref_known(v___x_56_, 2);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_48_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_55_);
v___x_60_ = l_Lean_Json_mkObj(v___x_59_);
lean_dec_ref_known(v___x_59_, 2);
return v___x_60_;
}
}
}
else
{
lean_object* v_module_63_; lean_object* v_name_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_87_; 
v_module_63_ = lean_ctor_get(v_x_43_, 0);
v_name_64_ = lean_ctor_get(v_x_43_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_87_ == 0)
{
v___x_66_ = v_x_43_;
v_isShared_67_ = v_isSharedCheck_87_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_name_64_);
lean_inc(v_module_63_);
lean_dec(v_x_43_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_87_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_68_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__2));
v___x_69_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0));
v___x_70_ = 1;
v___x_71_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_63_, v___x_70_);
v___x_72_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 0);
lean_ctor_set(v___x_66_, 1, v___x_72_);
lean_ctor_set(v___x_66_, 0, v___x_69_);
v___x_74_ = v___x_66_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_86_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_75_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_76_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_64_, v___x_70_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_box(0);
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_74_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = l_Lean_Json_mkObj(v___x_81_);
lean_dec_ref_known(v___x_81_, 2);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_68_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_79_);
v___x_85_ = l_Lean_Json_mkObj(v___x_84_);
lean_dec_ref_known(v___x_84_, 2);
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___impl(lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_tag_nat(v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___impl___boxed(lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Linter_CodeQuality_Value_ctorIdx___impl(v_x_92_);
lean_dec_ref(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(lean_object* v_t_94_, lean_object* v_k_95_){
_start:
{
if (lean_obj_tag(v_t_94_) == 0)
{
double v_value_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_value_96_ = lean_ctor_get_float(v_t_94_, 0);
lean_dec_ref_known(v_t_94_, 0);
v___x_97_ = lean_box_float(v_value_96_);
v___x_98_ = lean_apply_1(v_k_95_, v___x_97_);
return v___x_98_;
}
else
{
lean_object* v_dictionary_99_; lean_object* v___x_100_; 
v_dictionary_99_ = lean_ctor_get(v_t_94_, 0);
lean_inc(v_dictionary_99_);
lean_dec_ref_known(v_t_94_, 1);
v___x_100_ = lean_apply_1(v_k_95_, v_dictionary_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim(lean_object* v_motive_101_, lean_object* v_ctorIdx_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_103_, v_k_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___boxed(lean_object* v_motive_107_, lean_object* v_ctorIdx_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_k_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Linter_CodeQuality_Value_ctorElim(v_motive_107_, v_ctorIdx_108_, v_t_109_, v_h_110_, v_k_111_);
lean_dec(v_ctorIdx_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim___redArg(lean_object* v_t_113_, lean_object* v_scalar_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_113_, v_scalar_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_scalar_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_117_, v_scalar_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim___redArg(lean_object* v_t_121_, lean_object* v_dict_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_121_, v_dict_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_dict_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_125_, v_dict_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(lean_object* v_t_129_){
_start:
{
if (lean_obj_tag(v_t_129_) == 0)
{
lean_object* v_size_130_; lean_object* v_k_131_; lean_object* v_v_132_; lean_object* v_l_133_; lean_object* v_r_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_145_; 
v_size_130_ = lean_ctor_get(v_t_129_, 0);
v_k_131_ = lean_ctor_get(v_t_129_, 1);
v_v_132_ = lean_ctor_get(v_t_129_, 2);
v_l_133_ = lean_ctor_get(v_t_129_, 3);
v_r_134_ = lean_ctor_get(v_t_129_, 4);
v_isSharedCheck_145_ = !lean_is_exclusive(v_t_129_);
if (v_isSharedCheck_145_ == 0)
{
v___x_136_ = v_t_129_;
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_r_134_);
lean_inc(v_l_133_);
lean_inc(v_v_132_);
lean_inc(v_k_131_);
lean_inc(v_size_130_);
lean_dec(v_t_129_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
double v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_138_ = lean_unbox_float(v_v_132_);
lean_dec(v_v_132_);
v___x_139_ = l_Lean_Float_toJson(v___x_138_);
v___x_140_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_l_133_);
v___x_141_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_r_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 4, v___x_141_);
lean_ctor_set(v___x_136_, 3, v___x_140_);
lean_ctor_set(v___x_136_, 2, v___x_139_);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_size_130_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_131_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v___x_146_; 
v___x_146_ = lean_box(1);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(lean_object* v_map_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_map_147_);
v___x_149_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson(lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
double v_value_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_value_155_ = lean_ctor_get_float(v_x_154_, 0);
lean_dec_ref_known(v_x_154_, 0);
v___x_156_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__0));
v___x_157_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1));
v___x_158_ = l_Lean_Float_toJson(v_value_155_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_Json_mkObj(v___x_161_);
lean_dec_ref_known(v___x_161_, 2);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_156_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_160_);
v___x_165_ = l_Lean_Json_mkObj(v___x_164_);
lean_dec_ref_known(v___x_164_, 2);
return v___x_165_;
}
else
{
lean_object* v_dictionary_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_dictionary_166_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_dictionary_166_);
lean_dec_ref_known(v_x_154_, 1);
v___x_167_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__2));
v___x_168_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__3));
v___x_169_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(v_dictionary_166_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Lean_Json_mkObj(v___x_172_);
lean_dec_ref_known(v___x_172_, 2);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_167_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_171_);
v___x_176_ = l_Lean_Json_mkObj(v___x_175_);
lean_dec_ref_known(v___x_175_, 2);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
if (lean_obj_tag(v_a_179_) == 0)
{
lean_object* v___x_181_; 
v___x_181_ = lean_array_to_list(v_a_180_);
return v___x_181_;
}
else
{
lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v___x_184_; 
v_head_182_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_head_182_);
v_tail_183_ = lean_ctor_get(v_a_179_, 1);
lean_inc(v_tail_183_);
lean_dec_ref_known(v_a_179_, 2);
v___x_184_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_180_, v_head_182_);
v_a_179_ = v_tail_183_;
v_a_180_ = v___x_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(lean_object* v_x_189_){
_start:
{
lean_object* v_name_190_; lean_object* v_source_191_; lean_object* v_value_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_name_190_ = lean_ctor_get(v_x_189_, 0);
lean_inc_ref(v_name_190_);
v_source_191_ = lean_ctor_get(v_x_189_, 1);
lean_inc_ref(v_source_191_);
v_value_192_ = lean_ctor_get(v_x_189_, 2);
lean_inc_ref(v_value_192_);
lean_dec_ref(v_x_189_);
v___x_193_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_194_, 0, v_name_190_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__0));
v___x_199_ = l_Lean_Linter_CodeQuality_instToJsonSource_toJson(v_source_191_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_196_);
v___x_202_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1));
v___x_203_ = l_Lean_Linter_CodeQuality_instToJsonValue_toJson(v_value_192_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_196_);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_196_);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_201_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_197_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__1));
v___x_210_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(v___x_208_, v___x_209_);
v___x_211_ = l_Lean_Json_mkObj(v___x_210_);
lean_dec(v___x_210_);
return v___x_211_;
}
}
lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord(uint8_t builtin);
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_CodeQuality_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_CodeQuality_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_CodeQuality_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
