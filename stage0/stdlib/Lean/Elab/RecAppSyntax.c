// Lean compiler output
// Module: Lean.Elab.RecAppSyntax
// Imports: import Init.Data.String.Substring public import Lean.Expr
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_recApp"};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 14, 43, 140, 165, 123, 61, 74)}};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value;
static const lean_string_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_recAppPos"};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 195, 249, 168, 89, 177, 245, 31)}};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MData_isRecApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_isRecApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasRecAppSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo(lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v_pos_10_; lean_object* v_endPos_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v_pos_10_ = lean_ctor_get(v_x_9_, 1);
v_endPos_11_ = lean_ctor_get(v_x_9_, 3);
v___x_12_ = 1;
lean_inc(v_endPos_11_);
lean_inc(v_pos_10_);
v___x_13_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_13_, 0, v_pos_10_);
lean_ctor_set(v___x_13_, 1, v_endPos_11_);
lean_ctor_set_uint8(v___x_13_, sizeof(void*)*2, v___x_12_);
return v___x_13_;
}
else
{
lean_inc(v_x_9_);
return v_x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo___boxed(lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo(v_x_14_);
lean_dec(v_x_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax(lean_object* v_x_16_){
_start:
{
switch(lean_obj_tag(v_x_16_))
{
case 0:
{
return v_x_16_;
}
case 1:
{
lean_object* v_info_17_; lean_object* v_kind_18_; lean_object* v_args_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_30_; 
v_info_17_ = lean_ctor_get(v_x_16_, 0);
v_kind_18_ = lean_ctor_get(v_x_16_, 1);
v_args_19_ = lean_ctor_get(v_x_16_, 2);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_30_ == 0)
{
v___x_21_ = v_x_16_;
v_isShared_22_ = v_isSharedCheck_30_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_args_19_);
lean_inc(v_kind_18_);
lean_inc(v_info_17_);
lean_dec(v_x_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_30_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; size_t v_sz_24_; size_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_23_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo(v_info_17_);
lean_dec(v_info_17_);
v_sz_24_ = lean_array_size(v_args_19_);
v___x_25_ = ((size_t)0ULL);
v___x_26_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax_spec__0(v_sz_24_, v___x_25_, v_args_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_26_);
lean_ctor_set(v___x_21_, 0, v___x_23_);
v___x_28_ = v___x_21_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_kind_18_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
case 2:
{
lean_object* v_info_31_; lean_object* v_val_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_info_31_ = lean_ctor_get(v_x_16_, 0);
v_val_32_ = lean_ctor_get(v_x_16_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v_x_16_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_val_32_);
lean_inc(v_info_31_);
lean_dec(v_x_16_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo(v_info_31_);
lean_dec(v_info_31_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_val_32_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
default: 
{
lean_object* v_rawVal_41_; lean_object* v_info_42_; lean_object* v_val_43_; lean_object* v_preresolved_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_65_; 
v_rawVal_41_ = lean_ctor_get(v_x_16_, 1);
v_info_42_ = lean_ctor_get(v_x_16_, 0);
v_val_43_ = lean_ctor_get(v_x_16_, 2);
v_preresolved_44_ = lean_ctor_get(v_x_16_, 3);
v_isSharedCheck_65_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_65_ == 0)
{
v___x_46_ = v_x_16_;
v_isShared_47_ = v_isSharedCheck_65_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_preresolved_44_);
lean_inc(v_val_43_);
lean_inc(v_rawVal_41_);
lean_inc(v_info_42_);
lean_dec(v_x_16_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_65_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_str_48_; lean_object* v_startPos_49_; lean_object* v_stopPos_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_64_; 
v_str_48_ = lean_ctor_get(v_rawVal_41_, 0);
v_startPos_49_ = lean_ctor_get(v_rawVal_41_, 1);
v_stopPos_50_ = lean_ctor_get(v_rawVal_41_, 2);
v_isSharedCheck_64_ = !lean_is_exclusive(v_rawVal_41_);
if (v_isSharedCheck_64_ == 0)
{
v___x_52_ = v_rawVal_41_;
v_isShared_53_ = v_isSharedCheck_64_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_stopPos_50_);
lean_inc(v_startPos_49_);
lean_inc(v_str_48_);
lean_dec(v_rawVal_41_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_64_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_54_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSourceInfo(v_info_42_);
lean_dec(v_info_42_);
v___x_55_ = lean_string_utf8_extract(v_str_48_, v_startPos_49_, v_stopPos_50_);
lean_dec(v_stopPos_50_);
lean_dec(v_startPos_49_);
lean_dec_ref(v_str_48_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_string_utf8_byte_size(v___x_55_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 2, v___x_57_);
lean_ctor_set(v___x_52_, 1, v___x_56_);
lean_ctor_set(v___x_52_, 0, v___x_55_);
v___x_59_ = v___x_52_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v___x_57_);
v___x_59_ = v_reuseFailAlloc_63_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_61_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___x_59_);
lean_ctor_set(v___x_46_, 0, v___x_54_);
v___x_61_ = v___x_46_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v_val_43_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v_preresolved_44_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax_spec__0(size_t v_sz_66_, size_t v_i_67_, lean_object* v_bs_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_usize_dec_lt(v_i_67_, v_sz_66_);
if (v___x_69_ == 0)
{
return v_bs_68_;
}
else
{
lean_object* v_v_70_; lean_object* v___x_71_; lean_object* v_bs_x27_72_; lean_object* v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; 
v_v_70_ = lean_array_uget(v_bs_68_, v_i_67_);
v___x_71_ = lean_unsigned_to_nat(0u);
v_bs_x27_72_ = lean_array_uset(v_bs_68_, v_i_67_, v___x_71_);
v___x_73_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax(v_v_70_);
v___x_74_ = ((size_t)1ULL);
v___x_75_ = lean_usize_add(v_i_67_, v___x_74_);
v___x_76_ = lean_array_uset(v_bs_x27_72_, v_i_67_, v___x_73_);
v_i_67_ = v___x_75_;
v_bs_68_ = v___x_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax_spec__0___boxed(lean_object* v_sz_78_, lean_object* v_i_79_, lean_object* v_bs_80_){
_start:
{
size_t v_sz_boxed_81_; size_t v_i_boxed_82_; lean_object* v_res_83_; 
v_sz_boxed_81_ = lean_unbox_usize(v_sz_78_);
lean_dec(v_sz_78_);
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax_spec__0(v_sz_boxed_81_, v_i_boxed_82_, v_bs_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object* v_e_84_, lean_object* v_stx_85_){
_start:
{
lean_object* v_stx_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_m_90_; uint8_t v___x_91_; lean_object* v___x_92_; 
v_stx_86_ = l___private_Lean_Elab_RecAppSyntax_0__Lean_detachSyntax(v_stx_85_);
v___x_87_ = l_Lean_KVMap_empty;
v___x_88_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
lean_inc(v_stx_86_);
v___x_89_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_89_, 0, v_stx_86_);
v_m_90_ = l_Lean_KVMap_insert(v___x_87_, v___x_88_, v___x_89_);
v___x_91_ = 0;
v___x_92_ = l_Lean_Syntax_getPos_x3f(v_stx_86_, v___x_91_);
lean_dec(v_stx_86_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_mkMData(v_m_90_, v_e_84_);
return v___x_93_;
}
else
{
lean_object* v_val_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_104_; 
v_val_94_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_104_ == 0)
{
v___x_96_ = v___x_92_;
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_val_94_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey));
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 3);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_val_94_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = l_Lean_KVMap_insert(v_m_90_, v___x_98_, v___x_100_);
v___x_102_ = l_Lean_mkMData(v___x_101_, v_e_84_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object* v_e_105_){
_start:
{
if (lean_obj_tag(v_e_105_) == 10)
{
lean_object* v_data_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_data_106_ = lean_ctor_get(v_e_105_, 0);
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_108_ = l_Lean_KVMap_find(v_data_106_, v___x_107_);
if (lean_obj_tag(v___x_108_) == 1)
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_118_; 
v_val_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_118_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
if (lean_obj_tag(v_val_109_) == 5)
{
lean_object* v_v_113_; lean_object* v___x_115_; 
v_v_113_ = lean_ctor_get(v_val_109_, 0);
lean_inc(v_v_113_);
lean_dec_ref_known(v_val_109_, 1);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_v_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_v_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v___x_117_; 
lean_del_object(v___x_111_);
lean_dec(v_val_109_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
}
else
{
lean_object* v___x_119_; 
lean_dec(v___x_108_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
else
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object* v_e_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_getRecAppSyntax_x3f(v_e_121_);
lean_dec_ref(v_e_121_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_MData_isRecApp(lean_object* v_d_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_125_ = l_Lean_KVMap_contains(v_d_123_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MData_isRecApp___boxed(lean_object* v_d_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_MData_isRecApp(v_d_126_);
lean_dec(v_d_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_hasRecAppSyntax(lean_object* v_e_129_){
_start:
{
if (lean_obj_tag(v_e_129_) == 10)
{
lean_object* v_data_130_; uint8_t v___x_131_; 
v_data_130_ = lean_ctor_get(v_e_129_, 0);
v___x_131_ = l_Lean_MData_isRecApp(v_data_130_);
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object* v_e_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Lean_hasRecAppSyntax(v_e_133_);
lean_dec_ref(v_e_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_RecAppSyntax(builtin);
}
#ifdef __cplusplus
}
#endif
