// Lean compiler output
// Module: Lean.Linter.CodeQuality.Basic
// Imports: public import Init.Data.Float public import Std.Data.TreeMap public import Init.Data.Ord public import Lean.Data.Json
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
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Linter_CodeQuality_Source_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_name_8_; lean_object* v___x_9_; 
v_name_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_name_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_name_8_);
return v___x_9_;
}
else
{
lean_object* v_module_10_; lean_object* v_name_11_; lean_object* v___x_12_; 
v_module_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_module_10_);
v_name_11_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_name_11_);
lean_dec_ref_known(v_t_6_, 2);
v___x_12_ = lean_apply_2(v_k_7_, v_module_10_, v_name_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Linter_CodeQuality_Source_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim___redArg(lean_object* v_t_25_, lean_object* v_module_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_25_, v_module_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_module_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_29_, v_module_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim___redArg(lean_object* v_t_33_, lean_object* v_declaration_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_33_, v_declaration_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_declaration_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_37_, v_declaration_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson(lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_name_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_63_; 
v_name_45_ = lean_ctor_get(v_x_44_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_63_ == 0)
{
v___x_47_ = v_x_44_;
v_isShared_48_ = v_isSharedCheck_63_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_name_45_);
lean_dec(v_x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_63_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_49_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0));
v___x_50_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_51_ = 1;
v___x_52_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_45_, v___x_51_);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 3);
lean_ctor_set(v___x_47_, 0, v___x_52_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_62_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_50_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = l_Lean_Json_mkObj(v___x_57_);
lean_dec_ref_known(v___x_57_, 2);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_49_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_56_);
v___x_61_ = l_Lean_Json_mkObj(v___x_60_);
lean_dec_ref_known(v___x_60_, 2);
return v___x_61_;
}
}
}
else
{
lean_object* v_module_64_; lean_object* v_name_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_88_; 
v_module_64_ = lean_ctor_get(v_x_44_, 0);
v_name_65_ = lean_ctor_get(v_x_44_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_88_ == 0)
{
v___x_67_ = v_x_44_;
v_isShared_68_ = v_isSharedCheck_88_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_name_65_);
lean_inc(v_module_64_);
lean_dec(v_x_44_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_88_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_69_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__2));
v___x_70_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0));
v___x_71_ = 1;
v___x_72_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_64_, v___x_71_);
v___x_73_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 0);
lean_ctor_set(v___x_67_, 1, v___x_73_);
lean_ctor_set(v___x_67_, 0, v___x_70_);
v___x_75_ = v___x_67_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_73_);
v___x_75_ = v_reuseFailAlloc_87_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_76_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_77_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_65_, v___x_71_);
v___x_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_76_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_75_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = l_Lean_Json_mkObj(v___x_82_);
lean_dec_ref_known(v___x_82_, 2);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_69_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_80_);
v___x_86_ = l_Lean_Json_mkObj(v___x_85_);
lean_dec_ref_known(v___x_85_, 2);
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx(lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(0u);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(1u);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___boxed(lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Linter_CodeQuality_Value_ctorIdx(v_x_94_);
lean_dec_ref(v_x_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(lean_object* v_t_96_, lean_object* v_k_97_){
_start:
{
if (lean_obj_tag(v_t_96_) == 0)
{
double v_value_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_value_98_ = lean_ctor_get_float(v_t_96_, 0);
lean_dec_ref_known(v_t_96_, 0);
v___x_99_ = lean_box_float(v_value_98_);
v___x_100_ = lean_apply_1(v_k_97_, v___x_99_);
return v___x_100_;
}
else
{
lean_object* v_dictionary_101_; lean_object* v___x_102_; 
v_dictionary_101_ = lean_ctor_get(v_t_96_, 0);
lean_inc(v_dictionary_101_);
lean_dec_ref_known(v_t_96_, 1);
v___x_102_ = lean_apply_1(v_k_97_, v_dictionary_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim(lean_object* v_motive_103_, lean_object* v_ctorIdx_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_k_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_105_, v_k_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___boxed(lean_object* v_motive_109_, lean_object* v_ctorIdx_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_k_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Linter_CodeQuality_Value_ctorElim(v_motive_109_, v_ctorIdx_110_, v_t_111_, v_h_112_, v_k_113_);
lean_dec(v_ctorIdx_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim___redArg(lean_object* v_t_115_, lean_object* v_scalar_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_115_, v_scalar_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_scalar_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_119_, v_scalar_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim___redArg(lean_object* v_t_123_, lean_object* v_dict_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_123_, v_dict_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_dict_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_127_, v_dict_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(lean_object* v_t_131_){
_start:
{
if (lean_obj_tag(v_t_131_) == 0)
{
lean_object* v_size_132_; lean_object* v_k_133_; lean_object* v_v_134_; lean_object* v_l_135_; lean_object* v_r_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_147_; 
v_size_132_ = lean_ctor_get(v_t_131_, 0);
v_k_133_ = lean_ctor_get(v_t_131_, 1);
v_v_134_ = lean_ctor_get(v_t_131_, 2);
v_l_135_ = lean_ctor_get(v_t_131_, 3);
v_r_136_ = lean_ctor_get(v_t_131_, 4);
v_isSharedCheck_147_ = !lean_is_exclusive(v_t_131_);
if (v_isSharedCheck_147_ == 0)
{
v___x_138_ = v_t_131_;
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_r_136_);
lean_inc(v_l_135_);
lean_inc(v_v_134_);
lean_inc(v_k_133_);
lean_inc(v_size_132_);
lean_dec(v_t_131_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
double v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_140_ = lean_unbox_float(v_v_134_);
lean_dec(v_v_134_);
v___x_141_ = l_Lean_Float_toJson(v___x_140_);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_l_135_);
v___x_143_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_r_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 4, v___x_143_);
lean_ctor_set(v___x_138_, 3, v___x_142_);
lean_ctor_set(v___x_138_, 2, v___x_141_);
v___x_145_ = v___x_138_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_size_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_k_133_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(1);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(lean_object* v_map_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_map_149_);
v___x_151_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson(lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
double v_value_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_value_157_ = lean_ctor_get_float(v_x_156_, 0);
lean_dec_ref_known(v_x_156_, 0);
v___x_158_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__0));
v___x_159_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1));
v___x_160_ = l_Lean_Float_toJson(v_value_157_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Lean_Json_mkObj(v___x_163_);
lean_dec_ref_known(v___x_163_, 2);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_158_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_162_);
v___x_167_ = l_Lean_Json_mkObj(v___x_166_);
lean_dec_ref_known(v___x_166_, 2);
return v___x_167_;
}
else
{
lean_object* v_dictionary_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_dictionary_168_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_dictionary_168_);
lean_dec_ref_known(v_x_156_, 1);
v___x_169_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__2));
v___x_170_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__3));
v___x_171_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(v_dictionary_168_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Json_mkObj(v___x_174_);
lean_dec_ref_known(v___x_174_, 2);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_169_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_173_);
v___x_178_ = l_Lean_Json_mkObj(v___x_177_);
lean_dec_ref_known(v___x_177_, 2);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
if (lean_obj_tag(v_a_181_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_array_to_list(v_a_182_);
return v___x_183_;
}
else
{
lean_object* v_head_184_; lean_object* v_tail_185_; lean_object* v___x_186_; 
v_head_184_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_head_184_);
v_tail_185_ = lean_ctor_get(v_a_181_, 1);
lean_inc(v_tail_185_);
lean_dec_ref_known(v_a_181_, 2);
v___x_186_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_182_, v_head_184_);
v_a_181_ = v_tail_185_;
v_a_182_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(lean_object* v_x_191_){
_start:
{
lean_object* v_name_192_; lean_object* v_source_193_; lean_object* v_value_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_name_192_ = lean_ctor_get(v_x_191_, 0);
lean_inc_ref(v_name_192_);
v_source_193_ = lean_ctor_get(v_x_191_, 1);
lean_inc_ref(v_source_193_);
v_value_194_ = lean_ctor_get(v_x_191_, 2);
lean_inc_ref(v_value_194_);
lean_dec_ref(v_x_191_);
v___x_195_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_196_, 0, v_name_192_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__0));
v___x_201_ = l_Lean_Linter_CodeQuality_instToJsonSource_toJson(v_source_193_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_198_);
v___x_204_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1));
v___x_205_ = l_Lean_Linter_CodeQuality_instToJsonValue_toJson(v_value_194_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_198_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_198_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_203_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_199_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__1));
v___x_212_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(v___x_210_, v___x_211_);
v___x_213_ = l_Lean_Json_mkObj(v___x_212_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap(uint8_t builtin);
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
res = runtime_initialize_Std_Data_TreeMap(builtin);
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
lean_object* initialize_Std_Data_TreeMap(uint8_t builtin);
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
res = initialize_Std_Data_TreeMap(builtin);
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
