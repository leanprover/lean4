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
static lean_once_cell_t l_Lean_Compiler_isEagerLambdaLiftingName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
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
static lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0));
v___x_10_ = lean_string_utf8_byte_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isEagerLambdaLiftingName(lean_object* v_x_11_){
_start:
{
switch(lean_obj_tag(v_x_11_))
{
case 1:
{
lean_object* v_pre_12_; lean_object* v_str_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_pre_12_ = lean_ctor_get(v_x_11_, 0);
v_str_13_ = lean_ctor_get(v_x_11_, 1);
v___x_14_ = ((lean_object*)(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0));
v___x_15_ = lean_string_utf8_byte_size(v_str_13_);
v___x_16_ = lean_obj_once(&l_Lean_Compiler_isEagerLambdaLiftingName___closed__1, &l_Lean_Compiler_isEagerLambdaLiftingName___closed__1_once, _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1);
v___x_17_ = lean_nat_dec_le(v___x_16_, v___x_15_);
if (v___x_17_ == 0)
{
v_x_11_ = v_pre_12_;
goto _start;
}
else
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_string_memcmp(v_str_13_, v___x_14_, v___x_19_, v___x_19_, v___x_16_);
if (v___x_20_ == 0)
{
v_x_11_ = v_pre_12_;
goto _start;
}
else
{
return v___x_20_;
}
}
}
case 2:
{
lean_object* v_pre_22_; 
v_pre_22_ = lean_ctor_get(v_x_11_, 0);
v_x_11_ = v_pre_22_;
goto _start;
}
default: 
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_Compiler_isEagerLambdaLiftingName(v_x_25_);
lean_dec(v_x_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(size_t v_sz_28_, size_t v_i_29_, lean_object* v_bs_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_usize_dec_lt(v_i_29_, v_sz_28_);
if (v___x_31_ == 0)
{
return v_bs_30_;
}
else
{
lean_object* v_v_32_; lean_object* v_toConstantVal_33_; lean_object* v_name_34_; lean_object* v___x_35_; lean_object* v_bs_x27_36_; size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; 
v_v_32_ = lean_array_uget_borrowed(v_bs_30_, v_i_29_);
v_toConstantVal_33_ = lean_ctor_get(v_v_32_, 0);
v_name_34_ = lean_ctor_get(v_toConstantVal_33_, 0);
lean_inc(v_name_34_);
v___x_35_ = lean_unsigned_to_nat(0u);
v_bs_x27_36_ = lean_array_uset(v_bs_30_, v_i_29_, v___x_35_);
v___x_37_ = ((size_t)1ULL);
v___x_38_ = lean_usize_add(v_i_29_, v___x_37_);
v___x_39_ = lean_array_uset(v_bs_x27_36_, v_i_29_, v_name_34_);
v_i_29_ = v___x_38_;
v_bs_30_ = v___x_39_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0___boxed(lean_object* v_sz_41_, lean_object* v_i_42_, lean_object* v_bs_43_){
_start:
{
size_t v_sz_boxed_44_; size_t v_i_boxed_45_; lean_object* v_res_46_; 
v_sz_boxed_44_ = lean_unbox_usize(v_sz_41_);
lean_dec(v_sz_41_);
v_i_boxed_45_ = lean_unbox_usize(v_i_42_);
lean_dec(v_i_42_);
v_res_46_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_boxed_44_, v_i_boxed_45_, v_bs_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object* v_x_49_){
_start:
{
switch(lean_obj_tag(v_x_49_))
{
case 1:
{
lean_object* v_val_50_; lean_object* v_toConstantVal_51_; lean_object* v_name_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_val_50_ = lean_ctor_get(v_x_49_, 0);
lean_inc_ref(v_val_50_);
lean_dec_ref(v_x_49_);
v_toConstantVal_51_ = lean_ctor_get(v_val_50_, 0);
lean_inc_ref(v_toConstantVal_51_);
lean_dec_ref(v_val_50_);
v_name_52_ = lean_ctor_get(v_toConstantVal_51_, 0);
lean_inc(v_name_52_);
lean_dec_ref(v_toConstantVal_51_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_53_);
v___x_55_ = lean_array_push(v___x_54_, v_name_52_);
return v___x_55_;
}
case 3:
{
lean_object* v_val_56_; lean_object* v_toConstantVal_57_; lean_object* v_name_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_val_56_ = lean_ctor_get(v_x_49_, 0);
lean_inc_ref(v_val_56_);
lean_dec_ref(v_x_49_);
v_toConstantVal_57_ = lean_ctor_get(v_val_56_, 0);
lean_inc_ref(v_toConstantVal_57_);
lean_dec_ref(v_val_56_);
v_name_58_ = lean_ctor_get(v_toConstantVal_57_, 0);
lean_inc(v_name_58_);
lean_dec_ref(v_toConstantVal_57_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_array_push(v___x_60_, v_name_58_);
return v___x_61_;
}
case 0:
{
lean_object* v_val_62_; lean_object* v_toConstantVal_63_; lean_object* v_name_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_val_62_ = lean_ctor_get(v_x_49_, 0);
lean_inc_ref(v_val_62_);
lean_dec_ref(v_x_49_);
v_toConstantVal_63_ = lean_ctor_get(v_val_62_, 0);
lean_inc_ref(v_toConstantVal_63_);
lean_dec_ref(v_val_62_);
v_name_64_ = lean_ctor_get(v_toConstantVal_63_, 0);
lean_inc(v_name_64_);
lean_dec_ref(v_toConstantVal_63_);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_mk_empty_array_with_capacity(v___x_65_);
v___x_67_ = lean_array_push(v___x_66_, v_name_64_);
return v___x_67_;
}
case 5:
{
lean_object* v_defns_68_; lean_object* v___x_69_; size_t v_sz_70_; size_t v___x_71_; lean_object* v___x_72_; 
v_defns_68_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_defns_68_);
lean_dec_ref(v_x_49_);
v___x_69_ = lean_array_mk(v_defns_68_);
v_sz_70_ = lean_array_size(v___x_69_);
v___x_71_ = ((size_t)0ULL);
v___x_72_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_70_, v___x_71_, v___x_69_);
return v___x_72_;
}
default: 
{
lean_object* v___x_73_; 
lean_dec(v_x_49_);
v___x_73_ = ((lean_object*)(l_Lean_Compiler_getDeclNamesForCodeGen___closed__0));
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* v_env_80_, lean_object* v_n_81_){
_start:
{
uint8_t v___x_84_; lean_object* v___x_85_; 
v___x_84_ = 0;
lean_inc(v_n_81_);
v___x_85_ = l_Lean_Environment_findAsync_x3f(v_env_80_, v_n_81_, v___x_84_);
if (lean_obj_tag(v___x_85_) == 1)
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_100_; 
v_val_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_100_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_100_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_100_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint8_t v_kind_90_; 
v_kind_90_ = lean_ctor_get_uint8(v_val_86_, sizeof(void*)*3);
lean_dec(v_val_86_);
switch(v_kind_90_)
{
case 0:
{
lean_del_object(v___x_88_);
lean_dec(v_n_81_);
goto v___jp_82_;
}
case 3:
{
lean_del_object(v___x_88_);
lean_dec(v_n_81_);
goto v___jp_82_;
}
default: 
{
lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_91_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__1));
v___x_92_ = 1;
v___x_93_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_81_, v___x_92_);
v___x_94_ = lean_string_append(v___x_91_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__2));
v___x_96_ = lean_string_append(v___x_94_, v___x_95_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 0);
lean_ctor_set(v___x_88_, 0, v___x_96_);
v___x_98_ = v___x_88_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_85_);
v___x_101_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__3));
v___x_102_ = 1;
v___x_103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_81_, v___x_102_);
v___x_104_ = lean_string_append(v___x_101_, v___x_103_);
lean_dec_ref(v___x_103_);
v___x_105_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__4));
v___x_106_ = lean_string_append(v___x_104_, v___x_105_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
v___jp_82_:
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Lean_Compiler_checkIsDefinition___closed__0));
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object* v_declName_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Compiler_mkUnsafeRecName___closed__0));
v___x_111_ = l_Lean_Name_str___override(v_declName_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 1)
{
lean_object* v_pre_113_; lean_object* v_str_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_pre_113_ = lean_ctor_get(v_x_112_, 0);
v_str_114_ = lean_ctor_get(v_x_112_, 1);
v___x_115_ = ((lean_object*)(l_Lean_Compiler_mkUnsafeRecName___closed__0));
v___x_116_ = lean_string_dec_eq(v_str_114_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
lean_inc(v_pre_113_);
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v_pre_113_);
return v___x_118_;
}
}
else
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f___boxed(lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_x_120_);
lean_dec(v_x_120_);
return v_res_121_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Old(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
