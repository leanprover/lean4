// Lean compiler output
// Module: Lean.Compiler.Old
// Imports: public import Lean.Environment import Init.Data.String.TakeDrop
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
static const lean_string_object l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_elambda_"};
static const lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0 = (const lean_object*)&l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_elambda"};
static const lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__0 = (const lean_object*)&l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_isEagerLambdaLiftingName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_getDeclNamesForCodeGen___closed__0 = (const lean_object*)&l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
static const lean_ctor_object l_Lean_Compiler_checkIsDefinition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_checkIsDefinition___closed__0 = (const lean_object*)&l_Lean_Compiler_checkIsDefinition___closed__0_value;
static const lean_string_object l_Lean_Compiler_checkIsDefinition___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Declaration `"};
static const lean_object* l_Lean_Compiler_checkIsDefinition___closed__1 = (const lean_object*)&l_Lean_Compiler_checkIsDefinition___closed__1_value;
static const lean_string_object l_Lean_Compiler_checkIsDefinition___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l_Lean_Compiler_checkIsDefinition___closed__2 = (const lean_object*)&l_Lean_Compiler_checkIsDefinition___closed__2_value;
static const lean_string_object l_Lean_Compiler_checkIsDefinition___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Unknown declaration `"};
static const lean_object* l_Lean_Compiler_checkIsDefinition___closed__3 = (const lean_object*)&l_Lean_Compiler_checkIsDefinition___closed__3_value;
static const lean_string_object l_Lean_Compiler_checkIsDefinition___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Compiler_checkIsDefinition___closed__4 = (const lean_object*)&l_Lean_Compiler_checkIsDefinition___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_mkUnsafeRecName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_unsafe_rec"};
static const lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__0 = (const lean_object*)&l_Lean_Compiler_mkUnsafeRecName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName(lean_object* v_n_2_, lean_object* v_idx_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = ((lean_object*)(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0));
v___x_5_ = l_Nat_reprFast(v_idx_3_);
v___x_6_ = lean_string_append(v___x_4_, v___x_5_);
lean_dec_ref(v___x_5_);
v___x_7_ = l_Lean_Name_str___override(v_n_2_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isEagerLambdaLiftingName(lean_object* v_x_9_){
_start:
{
switch(lean_obj_tag(v_x_9_))
{
case 1:
{
lean_object* v_pre_10_; lean_object* v_str_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v_pre_10_ = lean_ctor_get(v_x_9_, 0);
v_str_11_ = lean_ctor_get(v_x_9_, 1);
v___x_12_ = lean_string_utf8_byte_size(v_str_11_);
v___x_13_ = lean_unsigned_to_nat(8u);
v___x_14_ = lean_nat_dec_le(v___x_13_, v___x_12_);
if (v___x_14_ == 0)
{
v_x_9_ = v_pre_10_;
goto _start;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_16_ = ((lean_object*)(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0));
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_string_memcmp(v_str_11_, v___x_16_, v___x_17_, v___x_17_, v___x_13_);
if (v___x_18_ == 0)
{
v_x_9_ = v_pre_10_;
goto _start;
}
else
{
return v___x_18_;
}
}
}
case 2:
{
lean_object* v_pre_20_; 
v_pre_20_ = lean_ctor_get(v_x_9_, 0);
v_x_9_ = v_pre_20_;
goto _start;
}
default: 
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_Compiler_isEagerLambdaLiftingName(v_x_23_);
lean_dec(v_x_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(size_t v_sz_26_, size_t v_i_27_, lean_object* v_bs_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_usize_dec_lt(v_i_27_, v_sz_26_);
if (v___x_29_ == 0)
{
return v_bs_28_;
}
else
{
lean_object* v_v_30_; lean_object* v_toConstantVal_31_; lean_object* v_name_32_; lean_object* v___x_33_; lean_object* v_bs_x27_34_; size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v_v_30_ = lean_array_uget_borrowed(v_bs_28_, v_i_27_);
v_toConstantVal_31_ = lean_ctor_get(v_v_30_, 0);
v_name_32_ = lean_ctor_get(v_toConstantVal_31_, 0);
lean_inc(v_name_32_);
v___x_33_ = lean_unsigned_to_nat(0u);
v_bs_x27_34_ = lean_array_uset(v_bs_28_, v_i_27_, v___x_33_);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_add(v_i_27_, v___x_35_);
v___x_37_ = lean_array_uset(v_bs_x27_34_, v_i_27_, v_name_32_);
v_i_27_ = v___x_36_;
v_bs_28_ = v___x_37_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0___boxed(lean_object* v_sz_39_, lean_object* v_i_40_, lean_object* v_bs_41_){
_start:
{
size_t v_sz_boxed_42_; size_t v_i_boxed_43_; lean_object* v_res_44_; 
v_sz_boxed_42_ = lean_unbox_usize(v_sz_39_);
lean_dec(v_sz_39_);
v_i_boxed_43_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_boxed_42_, v_i_boxed_43_, v_bs_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object* v_x_47_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 1:
{
lean_object* v_val_48_; lean_object* v_toConstantVal_49_; lean_object* v_name_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_val_48_ = lean_ctor_get(v_x_47_, 0);
lean_inc_ref(v_val_48_);
lean_dec_ref_known(v_x_47_, 1);
v_toConstantVal_49_ = lean_ctor_get(v_val_48_, 0);
lean_inc_ref(v_toConstantVal_49_);
lean_dec_ref(v_val_48_);
v_name_50_ = lean_ctor_get(v_toConstantVal_49_, 0);
lean_inc(v_name_50_);
lean_dec_ref(v_toConstantVal_49_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_mk_empty_array_with_capacity(v___x_51_);
v___x_53_ = lean_array_push(v___x_52_, v_name_50_);
return v___x_53_;
}
case 3:
{
lean_object* v_val_54_; lean_object* v_toConstantVal_55_; lean_object* v_name_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_val_54_ = lean_ctor_get(v_x_47_, 0);
lean_inc_ref(v_val_54_);
lean_dec_ref_known(v_x_47_, 1);
v_toConstantVal_55_ = lean_ctor_get(v_val_54_, 0);
lean_inc_ref(v_toConstantVal_55_);
lean_dec_ref(v_val_54_);
v_name_56_ = lean_ctor_get(v_toConstantVal_55_, 0);
lean_inc(v_name_56_);
lean_dec_ref(v_toConstantVal_55_);
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_mk_empty_array_with_capacity(v___x_57_);
v___x_59_ = lean_array_push(v___x_58_, v_name_56_);
return v___x_59_;
}
case 0:
{
lean_object* v_val_60_; lean_object* v_toConstantVal_61_; lean_object* v_name_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_val_60_ = lean_ctor_get(v_x_47_, 0);
lean_inc_ref(v_val_60_);
lean_dec_ref_known(v_x_47_, 1);
v_toConstantVal_61_ = lean_ctor_get(v_val_60_, 0);
lean_inc_ref(v_toConstantVal_61_);
lean_dec_ref(v_val_60_);
v_name_62_ = lean_ctor_get(v_toConstantVal_61_, 0);
lean_inc(v_name_62_);
lean_dec_ref(v_toConstantVal_61_);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_mk_empty_array_with_capacity(v___x_63_);
v___x_65_ = lean_array_push(v___x_64_, v_name_62_);
return v___x_65_;
}
case 5:
{
lean_object* v_defns_66_; lean_object* v___x_67_; size_t v_sz_68_; size_t v___x_69_; lean_object* v___x_70_; 
v_defns_66_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_defns_66_);
lean_dec_ref_known(v_x_47_, 1);
v___x_67_ = lean_array_mk(v_defns_66_);
v_sz_68_ = lean_array_size(v___x_67_);
v___x_69_ = ((size_t)0ULL);
v___x_70_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_68_, v___x_69_, v___x_67_);
return v___x_70_;
}
default: 
{
lean_object* v___x_71_; 
lean_dec(v_x_47_);
v___x_71_ = ((lean_object*)(l_Lean_Compiler_getDeclNamesForCodeGen___closed__0));
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* v_env_78_, lean_object* v_n_79_){
_start:
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = 0;
lean_inc(v_n_79_);
v___x_83_ = l_Lean_Environment_findAsync_x3f(v_env_78_, v_n_79_, v___x_82_);
if (lean_obj_tag(v___x_83_) == 1)
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_98_; 
v_val_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_98_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_98_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_98_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v_kind_88_; 
v_kind_88_ = lean_ctor_get_uint8(v_val_84_, sizeof(void*)*3);
lean_dec(v_val_84_);
switch(v_kind_88_)
{
case 0:
{
lean_del_object(v___x_86_);
lean_dec(v_n_79_);
goto v___jp_80_;
}
case 3:
{
lean_del_object(v___x_86_);
lean_dec(v_n_79_);
goto v___jp_80_;
}
default: 
{
lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_89_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__1));
v___x_90_ = 1;
v___x_91_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_79_, v___x_90_);
v___x_92_ = lean_string_append(v___x_89_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__2));
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 0);
lean_ctor_set(v___x_86_, 0, v___x_94_);
v___x_96_ = v___x_86_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v___x_83_);
v___x_99_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__3));
v___x_100_ = 1;
v___x_101_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_79_, v___x_100_);
v___x_102_ = lean_string_append(v___x_99_, v___x_101_);
lean_dec_ref(v___x_101_);
v___x_103_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__4));
v___x_104_ = lean_string_append(v___x_102_, v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
v___jp_80_:
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__0));
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object* v_declName_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_Compiler_mkUnsafeRecName___closed__0));
v___x_109_ = l_Lean_Name_str___override(v_declName_107_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 1)
{
lean_object* v_pre_111_; lean_object* v_str_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_pre_111_ = lean_ctor_get(v_x_110_, 0);
v_str_112_ = lean_ctor_get(v_x_110_, 1);
v___x_113_ = ((lean_object*)(l_Lean_Compiler_mkUnsafeRecName___closed__0));
v___x_114_ = lean_string_dec_eq(v_str_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
lean_inc(v_pre_111_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_pre_111_);
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f___boxed(lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_x_118_);
lean_dec(v_x_118_);
return v_res_119_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Old(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Old(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Old(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Old(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Old(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Old(builtin);
}
#ifdef __cplusplus
}
#endif
