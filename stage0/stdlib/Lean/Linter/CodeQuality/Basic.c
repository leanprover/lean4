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
lean_object* v_name_8_; lean_object* v___x_9_; 
v_name_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_name_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_name_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Linter_CodeQuality_Source_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim___redArg(lean_object* v_t_22_, lean_object* v_module_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_22_, v_module_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_module_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_module_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_26_, v_module_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim___redArg(lean_object* v_t_30_, lean_object* v_declaration_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_30_, v_declaration_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Source_declaration_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_declaration_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Linter_CodeQuality_Source_ctorElim___redArg(v_t_34_, v_declaration_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonSource_toJson(lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_object* v_name_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_60_; 
v_name_42_ = lean_ctor_get(v_x_41_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_60_ == 0)
{
v___x_44_ = v_x_41_;
v_isShared_45_ = v_isSharedCheck_60_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_name_42_);
lean_dec(v_x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_60_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_46_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__0));
v___x_47_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_48_ = 1;
v___x_49_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_42_, v___x_48_);
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 3);
lean_ctor_set(v___x_44_, 0, v___x_49_);
v___x_51_ = v___x_44_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_59_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_47_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = l_Lean_Json_mkObj(v___x_54_);
lean_dec_ref_known(v___x_54_, 2);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_46_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_53_);
v___x_58_ = l_Lean_Json_mkObj(v___x_57_);
lean_dec_ref_known(v___x_57_, 2);
return v___x_58_;
}
}
}
else
{
lean_object* v_name_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_79_; 
v_name_61_ = lean_ctor_get(v_x_41_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_79_ == 0)
{
v___x_63_ = v_x_41_;
v_isShared_64_ = v_isSharedCheck_79_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_name_61_);
lean_dec(v_x_41_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_79_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_65_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__2));
v___x_66_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_67_ = 1;
v___x_68_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_61_, v___x_67_);
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 3);
lean_ctor_set(v___x_63_, 0, v___x_68_);
v___x_70_ = v___x_63_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_78_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_66_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = l_Lean_Json_mkObj(v___x_73_);
lean_dec_ref_known(v___x_73_, 2);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_65_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_72_);
v___x_77_ = l_Lean_Json_mkObj(v___x_76_);
lean_dec_ref_known(v___x_76_, 2);
return v___x_77_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx(lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_unsigned_to_nat(0u);
return v___x_83_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = lean_unsigned_to_nat(1u);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorIdx___boxed(lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Linter_CodeQuality_Value_ctorIdx(v_x_85_);
lean_dec_ref(v_x_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(lean_object* v_t_87_, lean_object* v_k_88_){
_start:
{
if (lean_obj_tag(v_t_87_) == 0)
{
double v_value_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_value_89_ = lean_ctor_get_float(v_t_87_, 0);
lean_dec_ref_known(v_t_87_, 0);
v___x_90_ = lean_box_float(v_value_89_);
v___x_91_ = lean_apply_1(v_k_88_, v___x_90_);
return v___x_91_;
}
else
{
lean_object* v_dictionary_92_; lean_object* v___x_93_; 
v_dictionary_92_ = lean_ctor_get(v_t_87_, 0);
lean_inc(v_dictionary_92_);
lean_dec_ref_known(v_t_87_, 1);
v___x_93_ = lean_apply_1(v_k_88_, v_dictionary_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim(lean_object* v_motive_94_, lean_object* v_ctorIdx_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_k_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_96_, v_k_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_ctorElim___boxed(lean_object* v_motive_100_, lean_object* v_ctorIdx_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_k_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Linter_CodeQuality_Value_ctorElim(v_motive_100_, v_ctorIdx_101_, v_t_102_, v_h_103_, v_k_104_);
lean_dec(v_ctorIdx_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim___redArg(lean_object* v_t_106_, lean_object* v_scalar_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_106_, v_scalar_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_scalar_elim(lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_scalar_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_110_, v_scalar_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim___redArg(lean_object* v_t_114_, lean_object* v_dict_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_114_, v_dict_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_Value_dict_elim(lean_object* v_motive_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_dict_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Linter_CodeQuality_Value_ctorElim___redArg(v_t_118_, v_dict_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(lean_object* v_t_122_){
_start:
{
if (lean_obj_tag(v_t_122_) == 0)
{
lean_object* v_size_123_; lean_object* v_k_124_; lean_object* v_v_125_; lean_object* v_l_126_; lean_object* v_r_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_138_; 
v_size_123_ = lean_ctor_get(v_t_122_, 0);
v_k_124_ = lean_ctor_get(v_t_122_, 1);
v_v_125_ = lean_ctor_get(v_t_122_, 2);
v_l_126_ = lean_ctor_get(v_t_122_, 3);
v_r_127_ = lean_ctor_get(v_t_122_, 4);
v_isSharedCheck_138_ = !lean_is_exclusive(v_t_122_);
if (v_isSharedCheck_138_ == 0)
{
v___x_129_ = v_t_122_;
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_r_127_);
lean_inc(v_l_126_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
lean_inc(v_size_123_);
lean_dec(v_t_122_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
double v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_131_ = lean_unbox_float(v_v_125_);
lean_dec(v_v_125_);
v___x_132_ = l_Lean_Float_toJson(v___x_131_);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_l_126_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_r_127_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_134_);
lean_ctor_set(v___x_129_, 3, v___x_133_);
lean_ctor_set(v___x_129_, 2, v___x_132_);
v___x_136_ = v___x_129_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(1);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(lean_object* v_map_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0_spec__0(v_map_140_);
v___x_142_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonValue_toJson(lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
double v_value_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_value_148_ = lean_ctor_get_float(v_x_147_, 0);
lean_dec_ref_known(v_x_147_, 0);
v___x_149_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__0));
v___x_150_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1));
v___x_151_ = l_Lean_Float_toJson(v_value_148_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = l_Lean_Json_mkObj(v___x_154_);
lean_dec_ref_known(v___x_154_, 2);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_149_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_153_);
v___x_158_ = l_Lean_Json_mkObj(v___x_157_);
lean_dec_ref_known(v___x_157_, 2);
return v___x_158_;
}
else
{
lean_object* v_dictionary_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_dictionary_159_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_dictionary_159_);
lean_dec_ref_known(v_x_147_, 1);
v___x_160_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__2));
v___x_161_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__3));
v___x_162_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Linter_CodeQuality_instToJsonValue_toJson_spec__0(v_dictionary_159_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_Json_mkObj(v___x_165_);
lean_dec_ref_known(v___x_165_, 2);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_160_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_164_);
v___x_169_ = l_Lean_Json_mkObj(v___x_168_);
lean_dec_ref_known(v___x_168_, 2);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
if (lean_obj_tag(v_a_172_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_array_to_list(v_a_173_);
return v___x_174_;
}
else
{
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v___x_177_; 
v_head_175_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_head_175_);
v_tail_176_ = lean_ctor_get(v_a_172_, 1);
lean_inc(v_tail_176_);
lean_dec_ref_known(v_a_172_, 2);
v___x_177_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_173_, v_head_175_);
v_a_172_ = v_tail_176_;
v_a_173_ = v___x_177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(lean_object* v_x_182_){
_start:
{
lean_object* v_name_183_; lean_object* v_source_184_; lean_object* v_value_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_name_183_ = lean_ctor_get(v_x_182_, 0);
lean_inc_ref(v_name_183_);
v_source_184_ = lean_ctor_get(v_x_182_, 1);
lean_inc_ref(v_source_184_);
v_value_185_ = lean_ctor_get(v_x_182_, 2);
lean_inc_ref(v_value_185_);
lean_dec_ref(v_x_182_);
v___x_186_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonSource_toJson___closed__1));
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v_name_183_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__0));
v___x_192_ = l_Lean_Linter_CodeQuality_instToJsonSource_toJson(v_source_184_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_189_);
v___x_195_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonValue_toJson___closed__1));
v___x_196_ = l_Lean_Linter_CodeQuality_instToJsonValue_toJson(v_value_185_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_189_);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_189_);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_194_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_190_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = ((lean_object*)(l_Lean_Linter_CodeQuality_instToJsonEntry_toJson___closed__1));
v___x_203_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Linter_CodeQuality_instToJsonEntry_toJson_spec__0(v___x_201_, v___x_202_);
v___x_204_ = l_Lean_Json_mkObj(v___x_203_);
lean_dec(v___x_203_);
return v___x_204_;
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
