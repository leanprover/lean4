// Lean compiler output
// Module: Lake.Load.Lean
// Imports: public import Lake.Config.Package public import Lake.Load.Config import Lake.Load.Lean.Elab import Lake.Load.Lean.Eval
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
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_importConfigFile(lean_object*, lean_object*);
lean_object* l_Lake_PackageDecl_loadFromEnv(lean_object*, lean_object*);
lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_System_FilePath_normalize(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadLeanConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_loadLeanConfig___closed__0 = (const lean_object*)&l_Lake_loadLeanConfig___closed__0_value;
static const lean_string_object l_Lake_loadLeanConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".tar.gz"};
static const lean_object* l_Lake_loadLeanConfig___closed__1 = (const lean_object*)&l_Lake_loadLeanConfig___closed__1_value;
static const lean_array_object l_Lake_loadLeanConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadLeanConfig___closed__2 = (const lean_object*)&l_Lake_loadLeanConfig___closed__2_value;
static lean_once_cell_t l_Lake_loadLeanConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_loadLeanConfig___closed__3;
static lean_once_cell_t l_Lake_loadLeanConfig___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_loadLeanConfig___closed__4;
static lean_once_cell_t l_Lake_loadLeanConfig___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_loadLeanConfig___closed__5;
static lean_once_cell_t l_Lake_loadLeanConfig___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_loadLeanConfig___closed__6;
static lean_once_cell_t l_Lake_loadLeanConfig___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_loadLeanConfig___closed__7;
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg(lean_object* v_e_1_){
_start:
{
if (lean_obj_tag(v_e_1_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_a_3_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_e_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v_e_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_mk_io_user_error(v_a_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set_tag(v___x_5_, 1);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_a_12_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v_e_1_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_e_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 0);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg___boxed(lean_object* v_e_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg(v_e_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0(lean_object* v_00_u03b1_23_, lean_object* v_e_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg(v_e_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___boxed(lean_object* v_00_u03b1_27_, lean_object* v_e_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0(v_00_u03b1_27_, v_e_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1___redArg(lean_object* v_k_31_, lean_object* v_v_32_, lean_object* v_t_33_){
_start:
{
if (lean_obj_tag(v_t_33_) == 0)
{
lean_object* v_size_34_; lean_object* v_k_35_; lean_object* v_v_36_; lean_object* v_l_37_; lean_object* v_r_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_318_; 
v_size_34_ = lean_ctor_get(v_t_33_, 0);
v_k_35_ = lean_ctor_get(v_t_33_, 1);
v_v_36_ = lean_ctor_get(v_t_33_, 2);
v_l_37_ = lean_ctor_get(v_t_33_, 3);
v_r_38_ = lean_ctor_get(v_t_33_, 4);
v_isSharedCheck_318_ = !lean_is_exclusive(v_t_33_);
if (v_isSharedCheck_318_ == 0)
{
v___x_40_ = v_t_33_;
v_isShared_41_ = v_isSharedCheck_318_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_r_38_);
lean_inc(v_l_37_);
lean_inc(v_v_36_);
lean_inc(v_k_35_);
lean_inc(v_size_34_);
lean_dec(v_t_33_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_318_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
uint8_t v___x_42_; 
v___x_42_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_31_, v_k_35_);
switch(v___x_42_)
{
case 0:
{
lean_object* v_impl_43_; lean_object* v___x_44_; 
lean_dec(v_size_34_);
v_impl_43_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1___redArg(v_k_31_, v_v_32_, v_l_37_);
v___x_44_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_38_) == 0)
{
lean_object* v_size_45_; lean_object* v_size_46_; lean_object* v_k_47_; lean_object* v_v_48_; lean_object* v_l_49_; lean_object* v_r_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_size_45_ = lean_ctor_get(v_r_38_, 0);
v_size_46_ = lean_ctor_get(v_impl_43_, 0);
lean_inc(v_size_46_);
v_k_47_ = lean_ctor_get(v_impl_43_, 1);
lean_inc(v_k_47_);
v_v_48_ = lean_ctor_get(v_impl_43_, 2);
lean_inc(v_v_48_);
v_l_49_ = lean_ctor_get(v_impl_43_, 3);
lean_inc(v_l_49_);
v_r_50_ = lean_ctor_get(v_impl_43_, 4);
lean_inc(v_r_50_);
v___x_51_ = lean_unsigned_to_nat(3u);
v___x_52_ = lean_nat_mul(v___x_51_, v_size_45_);
v___x_53_ = lean_nat_dec_lt(v___x_52_, v_size_46_);
lean_dec(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
lean_dec(v_r_50_);
lean_dec(v_l_49_);
lean_dec(v_v_48_);
lean_dec(v_k_47_);
v___x_54_ = lean_nat_add(v___x_44_, v_size_46_);
lean_dec(v_size_46_);
v___x_55_ = lean_nat_add(v___x_54_, v_size_45_);
lean_dec(v___x_54_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 3, v_impl_43_);
lean_ctor_set(v___x_40_, 0, v___x_55_);
v___x_57_ = v___x_40_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_58_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_58_, 3, v_impl_43_);
lean_ctor_set(v_reuseFailAlloc_58_, 4, v_r_38_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
else
{
lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_124_; 
v_isSharedCheck_124_ = !lean_is_exclusive(v_impl_43_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; lean_object* v_unused_126_; lean_object* v_unused_127_; lean_object* v_unused_128_; lean_object* v_unused_129_; 
v_unused_125_ = lean_ctor_get(v_impl_43_, 4);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_impl_43_, 3);
lean_dec(v_unused_126_);
v_unused_127_ = lean_ctor_get(v_impl_43_, 2);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_impl_43_, 1);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_impl_43_, 0);
lean_dec(v_unused_129_);
v___x_60_ = v_impl_43_;
v_isShared_61_ = v_isSharedCheck_124_;
goto v_resetjp_59_;
}
else
{
lean_dec(v_impl_43_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_124_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_size_62_; lean_object* v_size_63_; lean_object* v_k_64_; lean_object* v_v_65_; lean_object* v_l_66_; lean_object* v_r_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_size_62_ = lean_ctor_get(v_l_49_, 0);
v_size_63_ = lean_ctor_get(v_r_50_, 0);
v_k_64_ = lean_ctor_get(v_r_50_, 1);
v_v_65_ = lean_ctor_get(v_r_50_, 2);
v_l_66_ = lean_ctor_get(v_r_50_, 3);
v_r_67_ = lean_ctor_get(v_r_50_, 4);
v___x_68_ = lean_unsigned_to_nat(2u);
v___x_69_ = lean_nat_mul(v___x_68_, v_size_62_);
v___x_70_ = lean_nat_dec_lt(v_size_63_, v___x_69_);
lean_dec(v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_99_; 
lean_inc(v_r_67_);
lean_inc(v_l_66_);
lean_inc(v_v_65_);
lean_inc(v_k_64_);
v_isSharedCheck_99_ = !lean_is_exclusive(v_r_50_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; lean_object* v_unused_104_; 
v_unused_100_ = lean_ctor_get(v_r_50_, 4);
lean_dec(v_unused_100_);
v_unused_101_ = lean_ctor_get(v_r_50_, 3);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_r_50_, 2);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_r_50_, 1);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_r_50_, 0);
lean_dec(v_unused_104_);
v___x_72_ = v_r_50_;
v_isShared_73_ = v_isSharedCheck_99_;
goto v_resetjp_71_;
}
else
{
lean_dec(v_r_50_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_99_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___x_87_; lean_object* v___y_89_; 
v___x_74_ = lean_nat_add(v___x_44_, v_size_46_);
lean_dec(v_size_46_);
v___x_75_ = lean_nat_add(v___x_74_, v_size_45_);
lean_dec(v___x_74_);
v___x_87_ = lean_nat_add(v___x_44_, v_size_62_);
if (lean_obj_tag(v_l_66_) == 0)
{
lean_object* v_size_97_; 
v_size_97_ = lean_ctor_get(v_l_66_, 0);
lean_inc(v_size_97_);
v___y_89_ = v_size_97_;
goto v___jp_88_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___y_89_ = v___x_98_;
goto v___jp_88_;
}
v___jp_76_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_nat_add(v___y_77_, v___y_79_);
lean_dec(v___y_79_);
lean_dec(v___y_77_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 4, v_r_38_);
lean_ctor_set(v___x_72_, 3, v_r_67_);
lean_ctor_set(v___x_72_, 2, v_v_36_);
lean_ctor_set(v___x_72_, 1, v_k_35_);
lean_ctor_set(v___x_72_, 0, v___x_80_);
v___x_82_ = v___x_72_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_r_67_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_r_38_);
v___x_82_ = v_reuseFailAlloc_86_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_84_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 4, v___x_82_);
lean_ctor_set(v___x_60_, 3, v___y_78_);
lean_ctor_set(v___x_60_, 2, v_v_65_);
lean_ctor_set(v___x_60_, 1, v_k_64_);
lean_ctor_set(v___x_60_, 0, v___x_75_);
v___x_84_ = v___x_60_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_v_65_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v___y_78_);
lean_ctor_set(v_reuseFailAlloc_85_, 4, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_nat_add(v___x_87_, v___y_89_);
lean_dec(v___y_89_);
lean_dec(v___x_87_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_l_66_);
lean_ctor_set(v___x_40_, 3, v_l_49_);
lean_ctor_set(v___x_40_, 2, v_v_48_);
lean_ctor_set(v___x_40_, 1, v_k_47_);
lean_ctor_set(v___x_40_, 0, v___x_90_);
v___x_92_ = v___x_40_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_k_47_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_v_48_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_l_49_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v_l_66_);
v___x_92_ = v_reuseFailAlloc_96_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_nat_add(v___x_44_, v_size_45_);
if (lean_obj_tag(v_r_67_) == 0)
{
lean_object* v_size_94_; 
v_size_94_ = lean_ctor_get(v_r_67_, 0);
lean_inc(v_size_94_);
v___y_77_ = v___x_93_;
v___y_78_ = v___x_92_;
v___y_79_ = v_size_94_;
goto v___jp_76_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___y_77_ = v___x_93_;
v___y_78_ = v___x_92_;
v___y_79_ = v___x_95_;
goto v___jp_76_;
}
}
}
}
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_del_object(v___x_40_);
v___x_105_ = lean_nat_add(v___x_44_, v_size_46_);
lean_dec(v_size_46_);
v___x_106_ = lean_nat_add(v___x_105_, v_size_45_);
lean_dec(v___x_105_);
v___x_107_ = lean_nat_add(v___x_44_, v_size_45_);
v___x_108_ = lean_nat_add(v___x_107_, v_size_63_);
lean_dec(v___x_107_);
lean_inc_ref(v_r_38_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 4, v_r_38_);
lean_ctor_set(v___x_60_, 3, v_r_50_);
lean_ctor_set(v___x_60_, 2, v_v_36_);
lean_ctor_set(v___x_60_, 1, v_k_35_);
lean_ctor_set(v___x_60_, 0, v___x_108_);
v___x_110_ = v___x_60_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v_r_50_);
lean_ctor_set(v_reuseFailAlloc_123_, 4, v_r_38_);
v___x_110_ = v_reuseFailAlloc_123_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_isSharedCheck_117_ = !lean_is_exclusive(v_r_38_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; lean_object* v_unused_119_; lean_object* v_unused_120_; lean_object* v_unused_121_; lean_object* v_unused_122_; 
v_unused_118_ = lean_ctor_get(v_r_38_, 4);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_r_38_, 3);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_r_38_, 2);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_r_38_, 1);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_r_38_, 0);
lean_dec(v_unused_122_);
v___x_112_ = v_r_38_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_r_38_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_110_);
lean_ctor_set(v___x_112_, 3, v_l_49_);
lean_ctor_set(v___x_112_, 2, v_v_48_);
lean_ctor_set(v___x_112_, 1, v_k_47_);
lean_ctor_set(v___x_112_, 0, v___x_106_);
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_47_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_48_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_l_49_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v___x_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_130_; 
v_l_130_ = lean_ctor_get(v_impl_43_, 3);
lean_inc(v_l_130_);
if (lean_obj_tag(v_l_130_) == 0)
{
lean_object* v_r_131_; lean_object* v_k_132_; lean_object* v_v_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_144_; 
v_r_131_ = lean_ctor_get(v_impl_43_, 4);
v_k_132_ = lean_ctor_get(v_impl_43_, 1);
v_v_133_ = lean_ctor_get(v_impl_43_, 2);
v_isSharedCheck_144_ = !lean_is_exclusive(v_impl_43_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_145_ = lean_ctor_get(v_impl_43_, 3);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_impl_43_, 0);
lean_dec(v_unused_146_);
v___x_135_ = v_impl_43_;
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_r_131_);
lean_inc(v_v_133_);
lean_inc(v_k_132_);
lean_dec(v_impl_43_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_144_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_131_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 3, v_r_131_);
lean_ctor_set(v___x_135_, 2, v_v_36_);
lean_ctor_set(v___x_135_, 1, v_k_35_);
lean_ctor_set(v___x_135_, 0, v___x_44_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_r_131_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_r_131_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v___x_139_);
lean_ctor_set(v___x_40_, 3, v_l_130_);
lean_ctor_set(v___x_40_, 2, v_v_133_);
lean_ctor_set(v___x_40_, 1, v_k_132_);
lean_ctor_set(v___x_40_, 0, v___x_137_);
v___x_141_ = v___x_40_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_k_132_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_v_133_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_l_130_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
else
{
lean_object* v_r_147_; 
v_r_147_ = lean_ctor_get(v_impl_43_, 4);
lean_inc(v_r_147_);
if (lean_obj_tag(v_r_147_) == 0)
{
lean_object* v_k_148_; lean_object* v_v_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_172_; 
v_k_148_ = lean_ctor_get(v_impl_43_, 1);
v_v_149_ = lean_ctor_get(v_impl_43_, 2);
v_isSharedCheck_172_ = !lean_is_exclusive(v_impl_43_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; 
v_unused_173_ = lean_ctor_get(v_impl_43_, 4);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_impl_43_, 3);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_impl_43_, 0);
lean_dec(v_unused_175_);
v___x_151_ = v_impl_43_;
v_isShared_152_ = v_isSharedCheck_172_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_v_149_);
lean_inc(v_k_148_);
lean_dec(v_impl_43_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_172_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_168_; 
v_k_153_ = lean_ctor_get(v_r_147_, 1);
v_v_154_ = lean_ctor_get(v_r_147_, 2);
v_isSharedCheck_168_ = !lean_is_exclusive(v_r_147_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; lean_object* v_unused_170_; lean_object* v_unused_171_; 
v_unused_169_ = lean_ctor_get(v_r_147_, 4);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_r_147_, 3);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_r_147_, 0);
lean_dec(v_unused_171_);
v___x_156_ = v_r_147_;
v_isShared_157_ = v_isSharedCheck_168_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_v_154_);
lean_inc(v_k_153_);
lean_dec(v_r_147_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_168_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(3u);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 4, v_l_130_);
lean_ctor_set(v___x_156_, 3, v_l_130_);
lean_ctor_set(v___x_156_, 2, v_v_149_);
lean_ctor_set(v___x_156_, 1, v_k_148_);
lean_ctor_set(v___x_156_, 0, v___x_44_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_v_149_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_l_130_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_l_130_);
v___x_160_ = v_reuseFailAlloc_167_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_l_130_);
lean_ctor_set(v___x_151_, 2, v_v_36_);
lean_ctor_set(v___x_151_, 1, v_k_35_);
lean_ctor_set(v___x_151_, 0, v___x_44_);
v___x_162_ = v___x_151_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_166_, 3, v_l_130_);
lean_ctor_set(v_reuseFailAlloc_166_, 4, v_l_130_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v___x_162_);
lean_ctor_set(v___x_40_, 3, v___x_160_);
lean_ctor_set(v___x_40_, 2, v_v_154_);
lean_ctor_set(v___x_40_, 1, v_k_153_);
lean_ctor_set(v___x_40_, 0, v___x_158_);
v___x_164_ = v___x_40_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(2u);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_r_147_);
lean_ctor_set(v___x_40_, 3, v_impl_43_);
lean_ctor_set(v___x_40_, 0, v___x_176_);
v___x_178_ = v___x_40_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_impl_43_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_r_147_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
case 1:
{
lean_object* v___x_181_; 
lean_dec(v_v_36_);
lean_dec(v_k_35_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 2, v_v_32_);
lean_ctor_set(v___x_40_, 1, v_k_31_);
v___x_181_ = v___x_40_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_size_34_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_k_31_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_v_32_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_l_37_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_r_38_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
default: 
{
lean_object* v_impl_183_; lean_object* v___x_184_; 
lean_dec(v_size_34_);
v_impl_183_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1___redArg(v_k_31_, v_v_32_, v_r_38_);
v___x_184_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_37_) == 0)
{
lean_object* v_size_185_; lean_object* v_size_186_; lean_object* v_k_187_; lean_object* v_v_188_; lean_object* v_l_189_; lean_object* v_r_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_size_185_ = lean_ctor_get(v_l_37_, 0);
v_size_186_ = lean_ctor_get(v_impl_183_, 0);
lean_inc(v_size_186_);
v_k_187_ = lean_ctor_get(v_impl_183_, 1);
lean_inc(v_k_187_);
v_v_188_ = lean_ctor_get(v_impl_183_, 2);
lean_inc(v_v_188_);
v_l_189_ = lean_ctor_get(v_impl_183_, 3);
lean_inc(v_l_189_);
v_r_190_ = lean_ctor_get(v_impl_183_, 4);
lean_inc(v_r_190_);
v___x_191_ = lean_unsigned_to_nat(3u);
v___x_192_ = lean_nat_mul(v___x_191_, v_size_185_);
v___x_193_ = lean_nat_dec_lt(v___x_192_, v_size_186_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
lean_dec(v_r_190_);
lean_dec(v_l_189_);
lean_dec(v_v_188_);
lean_dec(v_k_187_);
v___x_194_ = lean_nat_add(v___x_184_, v_size_185_);
v___x_195_ = lean_nat_add(v___x_194_, v_size_186_);
lean_dec(v_size_186_);
lean_dec(v___x_194_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_impl_183_);
lean_ctor_set(v___x_40_, 0, v___x_195_);
v___x_197_ = v___x_40_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_l_37_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v_impl_183_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
else
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_262_; 
v_isSharedCheck_262_ = !lean_is_exclusive(v_impl_183_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; lean_object* v_unused_264_; lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; 
v_unused_263_ = lean_ctor_get(v_impl_183_, 4);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_impl_183_, 3);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_impl_183_, 2);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_impl_183_, 1);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_impl_183_, 0);
lean_dec(v_unused_267_);
v___x_200_ = v_impl_183_;
v_isShared_201_ = v_isSharedCheck_262_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_impl_183_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_262_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_size_202_; lean_object* v_k_203_; lean_object* v_v_204_; lean_object* v_l_205_; lean_object* v_r_206_; lean_object* v_size_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_size_202_ = lean_ctor_get(v_l_189_, 0);
v_k_203_ = lean_ctor_get(v_l_189_, 1);
v_v_204_ = lean_ctor_get(v_l_189_, 2);
v_l_205_ = lean_ctor_get(v_l_189_, 3);
v_r_206_ = lean_ctor_get(v_l_189_, 4);
v_size_207_ = lean_ctor_get(v_r_190_, 0);
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = lean_nat_mul(v___x_208_, v_size_207_);
v___x_210_ = lean_nat_dec_lt(v_size_202_, v___x_209_);
lean_dec(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_238_; 
lean_inc(v_r_206_);
lean_inc(v_l_205_);
lean_inc(v_v_204_);
lean_inc(v_k_203_);
v_isSharedCheck_238_ = !lean_is_exclusive(v_l_189_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; 
v_unused_239_ = lean_ctor_get(v_l_189_, 4);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_l_189_, 3);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_l_189_, 2);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_l_189_, 1);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_l_189_, 0);
lean_dec(v_unused_243_);
v___x_212_ = v_l_189_;
v_isShared_213_ = v_isSharedCheck_238_;
goto v_resetjp_211_;
}
else
{
lean_dec(v_l_189_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_238_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_228_; 
v___x_214_ = lean_nat_add(v___x_184_, v_size_185_);
v___x_215_ = lean_nat_add(v___x_214_, v_size_186_);
lean_dec(v_size_186_);
if (lean_obj_tag(v_l_205_) == 0)
{
lean_object* v_size_236_; 
v_size_236_ = lean_ctor_get(v_l_205_, 0);
lean_inc(v_size_236_);
v___y_228_ = v_size_236_;
goto v___jp_227_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___y_228_ = v___x_237_;
goto v___jp_227_;
}
v___jp_216_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_nat_add(v___y_217_, v___y_219_);
lean_dec(v___y_219_);
lean_dec(v___y_217_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 4, v_r_190_);
lean_ctor_set(v___x_212_, 3, v_r_206_);
lean_ctor_set(v___x_212_, 2, v_v_188_);
lean_ctor_set(v___x_212_, 1, v_k_187_);
lean_ctor_set(v___x_212_, 0, v___x_220_);
v___x_222_ = v___x_212_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_k_187_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_v_188_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_r_206_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_r_190_);
v___x_222_ = v_reuseFailAlloc_226_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 4, v___x_222_);
lean_ctor_set(v___x_200_, 3, v___y_218_);
lean_ctor_set(v___x_200_, 2, v_v_204_);
lean_ctor_set(v___x_200_, 1, v_k_203_);
lean_ctor_set(v___x_200_, 0, v___x_215_);
v___x_224_ = v___x_200_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_203_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_204_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v___y_218_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_nat_add(v___x_214_, v___y_228_);
lean_dec(v___y_228_);
lean_dec(v___x_214_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_l_205_);
lean_ctor_set(v___x_40_, 0, v___x_229_);
v___x_231_ = v___x_40_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_l_37_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_l_205_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_nat_add(v___x_184_, v_size_207_);
if (lean_obj_tag(v_r_206_) == 0)
{
lean_object* v_size_233_; 
v_size_233_ = lean_ctor_get(v_r_206_, 0);
lean_inc(v_size_233_);
v___y_217_ = v___x_232_;
v___y_218_ = v___x_231_;
v___y_219_ = v_size_233_;
goto v___jp_216_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v___y_217_ = v___x_232_;
v___y_218_ = v___x_231_;
v___y_219_ = v___x_234_;
goto v___jp_216_;
}
}
}
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
lean_del_object(v___x_40_);
v___x_244_ = lean_nat_add(v___x_184_, v_size_185_);
v___x_245_ = lean_nat_add(v___x_244_, v_size_186_);
lean_dec(v_size_186_);
v___x_246_ = lean_nat_add(v___x_244_, v_size_202_);
lean_dec(v___x_244_);
lean_inc_ref(v_l_37_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 4, v_l_189_);
lean_ctor_set(v___x_200_, 3, v_l_37_);
lean_ctor_set(v___x_200_, 2, v_v_36_);
lean_ctor_set(v___x_200_, 1, v_k_35_);
lean_ctor_set(v___x_200_, 0, v___x_246_);
v___x_248_ = v___x_200_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_l_37_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_l_189_);
v___x_248_ = v_reuseFailAlloc_261_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_isSharedCheck_255_ = !lean_is_exclusive(v_l_37_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_256_ = lean_ctor_get(v_l_37_, 4);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_l_37_, 3);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_l_37_, 2);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_l_37_, 1);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_l_37_, 0);
lean_dec(v_unused_260_);
v___x_250_ = v_l_37_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_dec(v_l_37_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 4, v_r_190_);
lean_ctor_set(v___x_250_, 3, v___x_248_);
lean_ctor_set(v___x_250_, 2, v_v_188_);
lean_ctor_set(v___x_250_, 1, v_k_187_);
lean_ctor_set(v___x_250_, 0, v___x_245_);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_187_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_188_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_r_190_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_268_; 
v_l_268_ = lean_ctor_get(v_impl_183_, 3);
lean_inc(v_l_268_);
if (lean_obj_tag(v_l_268_) == 0)
{
lean_object* v_r_269_; lean_object* v_k_270_; lean_object* v_v_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v_r_269_ = lean_ctor_get(v_impl_183_, 4);
v_k_270_ = lean_ctor_get(v_impl_183_, 1);
v_v_271_ = lean_ctor_get(v_impl_183_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_impl_183_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; 
v_unused_295_ = lean_ctor_get(v_impl_183_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_impl_183_, 0);
lean_dec(v_unused_296_);
v___x_273_ = v_impl_183_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_r_269_);
lean_inc(v_v_271_);
lean_inc(v_k_270_);
lean_dec(v_impl_183_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_k_275_; lean_object* v_v_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_290_; 
v_k_275_ = lean_ctor_get(v_l_268_, 1);
v_v_276_ = lean_ctor_get(v_l_268_, 2);
v_isSharedCheck_290_ = !lean_is_exclusive(v_l_268_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_291_ = lean_ctor_get(v_l_268_, 4);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_l_268_, 3);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_l_268_, 0);
lean_dec(v_unused_293_);
v___x_278_ = v_l_268_;
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_v_276_);
lean_inc(v_k_275_);
lean_dec(v_l_268_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_269_, 2);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 4, v_r_269_);
lean_ctor_set(v___x_278_, 3, v_r_269_);
lean_ctor_set(v___x_278_, 2, v_v_36_);
lean_ctor_set(v___x_278_, 1, v_k_35_);
lean_ctor_set(v___x_278_, 0, v___x_184_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_r_269_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_r_269_);
v___x_282_ = v_reuseFailAlloc_289_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
lean_inc(v_r_269_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 3, v_r_269_);
lean_ctor_set(v___x_273_, 0, v___x_184_);
v___x_284_ = v___x_273_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_r_269_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_r_269_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v___x_284_);
lean_ctor_set(v___x_40_, 3, v___x_282_);
lean_ctor_set(v___x_40_, 2, v_v_276_);
lean_ctor_set(v___x_40_, 1, v_k_275_);
lean_ctor_set(v___x_40_, 0, v___x_280_);
v___x_286_ = v___x_40_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
else
{
lean_object* v_r_297_; 
v_r_297_ = lean_ctor_get(v_impl_183_, 4);
lean_inc(v_r_297_);
if (lean_obj_tag(v_r_297_) == 0)
{
lean_object* v_k_298_; lean_object* v_v_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
v_k_298_ = lean_ctor_get(v_impl_183_, 1);
v_v_299_ = lean_ctor_get(v_impl_183_, 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v_impl_183_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_311_ = lean_ctor_get(v_impl_183_, 4);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_impl_183_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_impl_183_, 0);
lean_dec(v_unused_313_);
v___x_301_ = v_impl_183_;
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_v_299_);
lean_inc(v_k_298_);
lean_dec(v_impl_183_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_unsigned_to_nat(3u);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 4, v_l_268_);
lean_ctor_set(v___x_301_, 2, v_v_36_);
lean_ctor_set(v___x_301_, 1, v_k_35_);
lean_ctor_set(v___x_301_, 0, v___x_184_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_l_268_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_l_268_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_r_297_);
lean_ctor_set(v___x_40_, 3, v___x_305_);
lean_ctor_set(v___x_40_, 2, v_v_299_);
lean_ctor_set(v___x_40_, 1, v_k_298_);
lean_ctor_set(v___x_40_, 0, v___x_303_);
v___x_307_ = v___x_40_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_k_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_v_299_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_r_297_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = lean_unsigned_to_nat(2u);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_impl_183_);
lean_ctor_set(v___x_40_, 3, v_r_297_);
lean_ctor_set(v___x_40_, 0, v___x_314_);
v___x_316_ = v___x_40_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_35_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_r_297_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_impl_183_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_k_31_);
lean_ctor_set(v___x_320_, 2, v_v_32_);
lean_ctor_set(v___x_320_, 3, v_t_33_);
lean_ctor_set(v___x_320_, 4, v_t_33_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg(lean_object* v_as_321_, size_t v_i_322_, size_t v_stop_323_, lean_object* v_b_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_eq(v_i_322_, v_stop_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v_name_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; 
v___x_326_ = lean_array_uget_borrowed(v_as_321_, v_i_322_);
v_name_327_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v___x_326_);
lean_inc(v_name_327_);
v___x_328_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1___redArg(v_name_327_, v___x_326_, v_b_324_);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_322_, v___x_329_);
v_i_322_ = v___x_330_;
v_b_324_ = v___x_328_;
goto _start;
}
else
{
return v_b_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg___boxed(lean_object* v_as_332_, lean_object* v_i_333_, lean_object* v_stop_334_, lean_object* v_b_335_){
_start:
{
size_t v_i_boxed_336_; size_t v_stop_boxed_337_; lean_object* v_res_338_; 
v_i_boxed_336_ = lean_unbox_usize(v_i_333_);
lean_dec(v_i_333_);
v_stop_boxed_337_ = lean_unbox_usize(v_stop_334_);
lean_dec(v_stop_334_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg(v_as_332_, v_i_boxed_336_, v_stop_boxed_337_, v_b_335_);
lean_dec_ref(v_as_332_);
return v_res_338_;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lake_loadLeanConfig___closed__2));
v___x_344_ = lean_array_get_size(v___x_343_);
return v___x_344_;
}
}
static uint8_t _init_l_Lake_loadLeanConfig___closed__4(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lake_loadLeanConfig___closed__3, &l_Lake_loadLeanConfig___closed__3_once, _init_l_Lake_loadLeanConfig___closed__3);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_nat_dec_lt(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static uint8_t _init_l_Lake_loadLeanConfig___closed__5(void){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lake_loadLeanConfig___closed__3, &l_Lake_loadLeanConfig___closed__3_once, _init_l_Lake_loadLeanConfig___closed__3);
v___x_349_ = lean_nat_dec_le(v___x_348_, v___x_348_);
return v___x_349_;
}
}
static size_t _init_l_Lake_loadLeanConfig___closed__6(void){
_start:
{
lean_object* v___x_350_; size_t v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lake_loadLeanConfig___closed__3, &l_Lake_loadLeanConfig___closed__3_once, _init_l_Lake_loadLeanConfig___closed__3);
v___x_351_ = lean_usize_of_nat(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lake_loadLeanConfig___closed__7(void){
_start:
{
lean_object* v___x_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_352_ = lean_box(1);
v___x_353_ = lean_usize_once(&l_Lake_loadLeanConfig___closed__6, &l_Lake_loadLeanConfig___closed__6_once, _init_l_Lake_loadLeanConfig___closed__6);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = ((lean_object*)(l_Lake_loadLeanConfig___closed__2));
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg(v___x_355_, v___x_354_, v___x_353_, v___x_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object* v_cfg_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
lean_inc_ref(v_cfg_357_);
v___x_360_ = l_Lake_importConfigFile(v_cfg_357_, v_a_358_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_461_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_a_362_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_461_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_461_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_461_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_pkgIdx_366_; lean_object* v_pkgName_367_; lean_object* v_relPkgDir_368_; lean_object* v_pkgDir_369_; lean_object* v_relConfigFile_370_; lean_object* v_configFile_371_; lean_object* v_leanOpts_372_; lean_object* v_scope_373_; lean_object* v_remoteUrl_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_pkgIdx_366_ = lean_ctor_get(v_cfg_357_, 3);
lean_inc(v_pkgIdx_366_);
v_pkgName_367_ = lean_ctor_get(v_cfg_357_, 4);
lean_inc(v_pkgName_367_);
v_relPkgDir_368_ = lean_ctor_get(v_cfg_357_, 5);
lean_inc_ref(v_relPkgDir_368_);
v_pkgDir_369_ = lean_ctor_get(v_cfg_357_, 6);
lean_inc_ref(v_pkgDir_369_);
v_relConfigFile_370_ = lean_ctor_get(v_cfg_357_, 7);
lean_inc_ref(v_relConfigFile_370_);
v_configFile_371_ = lean_ctor_get(v_cfg_357_, 8);
lean_inc_ref(v_configFile_371_);
v_leanOpts_372_ = lean_ctor_get(v_cfg_357_, 11);
lean_inc_ref(v_leanOpts_372_);
v_scope_373_ = lean_ctor_get(v_cfg_357_, 12);
lean_inc_ref(v_scope_373_);
v_remoteUrl_374_ = lean_ctor_get(v_cfg_357_, 13);
lean_inc_ref(v_remoteUrl_374_);
lean_dec_ref(v_cfg_357_);
lean_inc(v_a_361_);
v___x_375_ = l_Lake_PackageDecl_loadFromEnv(v_a_361_, v_leanOpts_372_);
v___x_376_ = l_IO_ofExcept___at___00Lake_loadLeanConfig_spec__0___redArg(v___x_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v_name_378_; lean_object* v_origName_379_; lean_object* v_config_380_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_447_; uint8_t v___x_451_; 
lean_del_object(v___x_364_);
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_376_);
v_name_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_name_378_);
v_origName_379_ = lean_ctor_get(v_a_377_, 1);
lean_inc(v_origName_379_);
v_config_380_ = lean_ctor_get(v_a_377_, 2);
lean_inc_ref(v_config_380_);
lean_dec(v_a_377_);
v___x_451_ = l_Lean_Name_isAnonymous(v_pkgName_367_);
if (v___x_451_ == 0)
{
v___y_447_ = v_pkgName_367_;
goto v___jp_446_;
}
else
{
lean_dec(v_pkgName_367_);
lean_inc(v_origName_379_);
v___y_447_ = v_origName_379_;
goto v___jp_446_;
}
v___jp_381_:
{
lean_object* v_testDriver_392_; lean_object* v_lintDriver_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_testDriver_392_ = lean_ctor_get(v_config_380_, 13);
lean_inc_ref(v_testDriver_392_);
v_lintDriver_393_ = lean_ctor_get(v_config_380_, 15);
lean_inc_ref(v_lintDriver_393_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v___x_395_, 0, v_pkgIdx_366_);
lean_ctor_set(v___x_395_, 1, v___y_388_);
lean_ctor_set(v___x_395_, 2, v_name_378_);
lean_ctor_set(v___x_395_, 3, v_origName_379_);
lean_ctor_set(v___x_395_, 4, v_pkgDir_369_);
lean_ctor_set(v___x_395_, 5, v_relPkgDir_368_);
lean_ctor_set(v___x_395_, 6, v_config_380_);
lean_ctor_set(v___x_395_, 7, v_configFile_371_);
lean_ctor_set(v___x_395_, 8, v_relConfigFile_370_);
lean_ctor_set(v___x_395_, 9, v___y_385_);
lean_ctor_set(v___x_395_, 10, v_scope_373_);
lean_ctor_set(v___x_395_, 11, v_remoteUrl_374_);
lean_ctor_set(v___x_395_, 12, v___y_383_);
lean_ctor_set(v___x_395_, 13, v___y_387_);
lean_ctor_set(v___x_395_, 14, v___y_382_);
lean_ctor_set(v___x_395_, 15, v___y_390_);
lean_ctor_set(v___x_395_, 16, v___y_386_);
lean_ctor_set(v___x_395_, 17, v___y_384_);
lean_ctor_set(v___x_395_, 18, v___y_389_);
lean_ctor_set(v___x_395_, 19, v___y_391_);
lean_ctor_set(v___x_395_, 20, v_testDriver_392_);
lean_ctor_set(v___x_395_, 21, v_lintDriver_393_);
lean_ctor_set(v___x_395_, 22, v___x_394_);
lean_ctor_set(v___x_395_, 23, v___x_394_);
lean_inc(v_a_361_);
v___x_396_ = l_Lake_Package_loadFromEnv(v___x_395_, v_a_361_, v_leanOpts_372_, v_a_362_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_a_398_ = lean_ctor_get(v___x_396_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_a_397_);
lean_ctor_set(v___x_402_, 1, v_a_361_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_a_398_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_a_361_);
v_a_407_ = lean_ctor_get(v___x_396_, 0);
v_a_408_ = lean_ctor_get(v___x_396_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_396_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_inc(v_a_407_);
lean_dec(v___x_396_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_407_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
v___jp_416_:
{
lean_object* v_buildArchive_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_buildArchive_423_ = lean_ctor_get(v_config_380_, 12);
v___x_424_ = lean_mk_empty_array_with_capacity(v___y_417_);
v___x_425_ = lean_box(1);
if (lean_obj_tag(v_buildArchive_423_) == 1)
{
lean_object* v_val_426_; 
v_val_426_ = lean_ctor_get(v_buildArchive_423_, 0);
lean_inc(v_val_426_);
lean_inc_ref_n(v___x_424_, 2);
v___y_382_ = v___y_422_;
v___y_383_ = v___y_418_;
v___y_384_ = v___x_424_;
v___y_385_ = v___y_419_;
v___y_386_ = v___x_425_;
v___y_387_ = v___y_420_;
v___y_388_ = v___y_421_;
v___y_389_ = v___x_424_;
v___y_390_ = v___x_424_;
v___y_391_ = v_val_426_;
goto v___jp_381_;
}
else
{
uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_427_ = 0;
lean_inc(v___y_421_);
v___x_428_ = l_Lean_Name_toString(v___y_421_, v___x_427_);
v___x_429_ = ((lean_object*)(l_Lake_loadLeanConfig___closed__0));
v___x_430_ = lean_string_append(v___x_428_, v___x_429_);
v___x_431_ = l_System_Platform_target;
v___x_432_ = lean_string_append(v___x_430_, v___x_431_);
v___x_433_ = ((lean_object*)(l_Lake_loadLeanConfig___closed__1));
v___x_434_ = lean_string_append(v___x_432_, v___x_433_);
lean_inc_ref_n(v___x_424_, 2);
v___y_382_ = v___y_422_;
v___y_383_ = v___y_418_;
v___y_384_ = v___x_424_;
v___y_385_ = v___y_419_;
v___y_386_ = v___x_425_;
v___y_387_ = v___y_420_;
v___y_388_ = v___y_421_;
v___y_389_ = v___x_424_;
v___y_390_ = v___x_424_;
v___y_391_ = v___x_434_;
goto v___jp_381_;
}
}
v___jp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_438_ = l_System_FilePath_normalize(v___y_437_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = ((lean_object*)(l_Lake_loadLeanConfig___closed__2));
v___x_441_ = lean_box(1);
v___x_442_ = lean_uint8_once(&l_Lake_loadLeanConfig___closed__4, &l_Lake_loadLeanConfig___closed__4_once, _init_l_Lake_loadLeanConfig___closed__4);
if (v___x_442_ == 0)
{
v___y_417_ = v___x_439_;
v___y_418_ = v___x_440_;
v___y_419_ = v___x_438_;
v___y_420_ = v___x_440_;
v___y_421_ = v___y_436_;
v___y_422_ = v___x_441_;
goto v___jp_416_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = lean_uint8_once(&l_Lake_loadLeanConfig___closed__5, &l_Lake_loadLeanConfig___closed__5_once, _init_l_Lake_loadLeanConfig___closed__5);
if (v___x_443_ == 0)
{
if (v___x_442_ == 0)
{
v___y_417_ = v___x_439_;
v___y_418_ = v___x_440_;
v___y_419_ = v___x_438_;
v___y_420_ = v___x_440_;
v___y_421_ = v___y_436_;
v___y_422_ = v___x_441_;
goto v___jp_416_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l_Lake_loadLeanConfig___closed__7, &l_Lake_loadLeanConfig___closed__7_once, _init_l_Lake_loadLeanConfig___closed__7);
v___y_417_ = v___x_439_;
v___y_418_ = v___x_440_;
v___y_419_ = v___x_438_;
v___y_420_ = v___x_440_;
v___y_421_ = v___y_436_;
v___y_422_ = v___x_444_;
goto v___jp_416_;
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Lake_loadLeanConfig___closed__7, &l_Lake_loadLeanConfig___closed__7_once, _init_l_Lake_loadLeanConfig___closed__7);
v___y_417_ = v___x_439_;
v___y_418_ = v___x_440_;
v___y_419_ = v___x_438_;
v___y_420_ = v___x_440_;
v___y_421_ = v___y_436_;
v___y_422_ = v___x_445_;
goto v___jp_416_;
}
}
}
v___jp_446_:
{
lean_object* v_manifestFile_448_; 
v_manifestFile_448_ = lean_ctor_get(v_config_380_, 2);
if (lean_obj_tag(v_manifestFile_448_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = l_Lake_defaultManifestFile;
v___y_436_ = v___y_447_;
v___y_437_ = v___x_449_;
goto v___jp_435_;
}
else
{
lean_object* v_val_450_; 
v_val_450_ = lean_ctor_get(v_manifestFile_448_, 0);
lean_inc(v_val_450_);
v___y_436_ = v___y_447_;
v___y_437_ = v_val_450_;
goto v___jp_435_;
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec_ref(v_remoteUrl_374_);
lean_dec_ref(v_scope_373_);
lean_dec_ref(v_leanOpts_372_);
lean_dec_ref(v_configFile_371_);
lean_dec_ref(v_relConfigFile_370_);
lean_dec_ref(v_pkgDir_369_);
lean_dec_ref(v_relPkgDir_368_);
lean_dec(v_pkgName_367_);
lean_dec(v_pkgIdx_366_);
lean_dec(v_a_361_);
v_a_452_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_376_);
v___x_453_ = lean_io_error_to_string(v_a_452_);
v___x_454_ = 3;
v___x_455_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*1, v___x_454_);
v___x_456_ = lean_array_get_size(v_a_362_);
v___x_457_ = lean_array_push(v_a_362_, v___x_455_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 1);
lean_ctor_set(v___x_364_, 1, v___x_457_);
lean_ctor_set(v___x_364_, 0, v___x_456_);
v___x_459_ = v___x_364_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_cfg_357_);
v_a_462_ = lean_ctor_get(v___x_360_, 0);
v_a_463_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_360_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_inc(v_a_462_);
lean_dec(v___x_360_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig___boxed(lean_object* v_cfg_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lake_loadLeanConfig(v_cfg_471_, v_a_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1(lean_object* v_00_u03b2_475_, lean_object* v_k_476_, lean_object* v_v_477_, lean_object* v_t_478_, lean_object* v_hl_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadLeanConfig_spec__1___redArg(v_k_476_, v_v_477_, v_t_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2(lean_object* v_name_481_, lean_object* v_as_482_, size_t v_i_483_, size_t v_stop_484_, lean_object* v_b_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___redArg(v_as_482_, v_i_483_, v_stop_484_, v_b_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2___boxed(lean_object* v_name_487_, lean_object* v_as_488_, lean_object* v_i_489_, lean_object* v_stop_490_, lean_object* v_b_491_){
_start:
{
size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_490_);
lean_dec(v_stop_490_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadLeanConfig_spec__2(v_name_487_, v_as_488_, v_i_boxed_492_, v_stop_boxed_493_, v_b_491_);
lean_dec_ref(v_as_488_);
lean_dec(v_name_487_);
return v_res_494_;
}
}
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Elab(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Lean(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Lean(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Lean(builtin);
}
#ifdef __cplusplus
}
#endif
