// Lean compiler output
// Module: Std.Time.Zoned.Database.Windows
// Imports: public import Init.Data.SInt.Basic public import Std.Time.Zoned.Database.Basic import Init.While
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
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
uint64_t lean_int64_of_nat(lean_object*);
uint64_t lean_int64_neg(uint64_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_windows_get_next_transition(lean_object*, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__0;
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_Windows_getZoneRules___closed__1;
static const lean_array_object l_Std_Time_Database_Windows_getZoneRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__2 = (const lean_object*)&l_Std_Time_Database_Windows_getZoneRules___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__3;
static const lean_string_object l_Std_Time_Database_Windows_getZoneRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "cannot find first transition in zone rules"};
static const lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__4 = (const lean_object*)&l_Std_Time_Database_Windows_getZoneRules___closed__4_value;
static lean_once_cell_t l_Std_Time_Database_Windows_getZoneRules___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Database_Windows_getZoneRules___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_default;
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Database_WindowsDb_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_WindowsDb_inst___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_WindowsDb_inst___closed__0 = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__0_value;
static const lean_closure_object l_Std_Time_Database_WindowsDb_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Database_WindowsDb_inst___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Database_WindowsDb_inst___closed__1 = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__1_value;
static const lean_ctor_object l_Std_Time_Database_WindowsDb_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__0_value),((lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__1_value)}};
static const lean_object* l_Std_Time_Database_WindowsDb_inst___closed__2 = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Database_WindowsDb_inst = (const lean_object*)&l_Std_Time_Database_WindowsDb_inst___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object* v_a_00___x40___internal___hyg_5_, lean_object* v_a_00___x40___internal___hyg_6_, lean_object* v_a_00___x40___internal___hyg_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_2__boxed_9_; uint8_t v_a_00___x40___internal___hyg_3__boxed_10_; lean_object* v_res_11_; 
v_a_00___x40___internal___hyg_2__boxed_9_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_6_);
lean_dec_ref(v_a_00___x40___internal___hyg_6_);
v_a_00___x40___internal___hyg_3__boxed_10_ = lean_unbox(v_a_00___x40___internal___hyg_7_);
v_res_11_ = lean_windows_get_next_transition(v_a_00___x40___internal___hyg_5_, v_a_00___x40___internal___hyg_2__boxed_9_, v_a_00___x40___internal___hyg_3__boxed_10_);
lean_dec_ref(v_a_00___x40___internal___hyg_5_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object* v_a_00___x40___internal___hyg_14_, lean_object* v_a_00___x40___internal___hyg_15_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_1__boxed_16_; lean_object* v_res_17_; 
v_a_00___x40___internal___hyg_1__boxed_16_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_14_);
lean_dec_ref(v_a_00___x40___internal___hyg_14_);
v_res_17_ = lean_get_windows_local_timezone_id_at(v_a_00___x40___internal___hyg_1__boxed_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object* v_res_18_){
_start:
{
lean_object* v_offset_19_; lean_object* v_name_20_; lean_object* v_abbreviation_21_; uint8_t v_isDST_22_; uint8_t v___x_23_; uint8_t v___x_24_; lean_object* v___x_25_; 
v_offset_19_ = lean_ctor_get(v_res_18_, 0);
v_name_20_ = lean_ctor_get(v_res_18_, 1);
v_abbreviation_21_ = lean_ctor_get(v_res_18_, 2);
v_isDST_22_ = lean_ctor_get_uint8(v_res_18_, sizeof(void*)*3);
v___x_23_ = 0;
v___x_24_ = 1;
lean_inc_ref(v_name_20_);
lean_inc_ref(v_abbreviation_21_);
lean_inc(v_offset_19_);
v___x_25_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_25_, 0, v_offset_19_);
lean_ctor_set(v___x_25_, 1, v_abbreviation_21_);
lean_ctor_set(v___x_25_, 2, v_name_20_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*3, v_isDST_22_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*3 + 1, v___x_23_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*3 + 2, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object* v_res_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_res_26_);
lean_dec_ref(v_res_26_);
return v_res_27_;
}
}
static uint64_t _init_l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_28_; uint64_t v___x_29_; 
v___x_28_ = lean_cstr_to_nat("32503690800");
v___x_29_ = lean_int64_of_nat(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(lean_object* v_id_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_fst_33_; lean_object* v_snd_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_90_; 
v_fst_33_ = lean_ctor_get(v_a_31_, 0);
v_snd_34_ = lean_ctor_get(v_a_31_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_31_);
if (v_isSharedCheck_90_ == 0)
{
v___x_36_ = v_a_31_;
v_isShared_37_ = v_isSharedCheck_90_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_snd_34_);
lean_inc(v_fst_33_);
lean_dec(v_a_31_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_90_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
uint8_t v___x_38_; uint64_t v___x_39_; lean_object* v___x_40_; 
v___x_38_ = 0;
v___x_39_ = lean_unbox_uint64(v_fst_33_);
v___x_40_ = lean_windows_get_next_transition(v_id_30_, v___x_39_, v___x_38_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_81_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_81_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_81_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_81_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
if (lean_obj_tag(v_a_41_) == 1)
{
lean_object* v_val_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_74_; 
lean_del_object(v___x_36_);
v_val_45_ = lean_ctor_get(v_a_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v_a_41_, 1);
v_fst_46_ = lean_ctor_get(v_val_45_, 0);
v_snd_47_ = lean_ctor_get(v_val_45_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v_val_45_);
if (v_isSharedCheck_74_ == 0)
{
v___x_49_ = v_val_45_;
v_isShared_50_ = v_isSharedCheck_74_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_snd_47_);
lean_inc(v_fst_46_);
lean_dec(v_val_45_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_74_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
uint64_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___y_57_; uint64_t v___x_68_; uint64_t v___x_69_; uint8_t v___x_70_; 
v___x_51_ = lean_unbox_uint64(v_fst_33_);
v___x_52_ = lean_int64_to_int_sint(v___x_51_);
v___x_53_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_47_);
lean_dec(v_snd_47_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_array_push(v_snd_34_, v___x_54_);
v___x_68_ = lean_unbox_uint64(v_fst_46_);
v___x_69_ = lean_unbox_uint64(v_fst_33_);
v___x_70_ = lean_int64_dec_le(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
uint64_t v___x_71_; uint64_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = lean_uint64_once(&l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0);
v___x_72_ = lean_unbox_uint64(v_fst_46_);
v___x_73_ = lean_int64_dec_le(v___x_71_, v___x_72_);
v___y_57_ = v___x_73_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___x_70_;
goto v___jp_56_;
}
v___jp_56_:
{
if (v___y_57_ == 0)
{
lean_object* v___x_59_; 
lean_del_object(v___x_43_);
lean_dec(v_fst_33_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v___x_55_);
v___x_59_ = v___x_49_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_fst_46_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_55_);
v___x_59_ = v_reuseFailAlloc_61_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
v_a_31_ = v___x_59_;
goto _start;
}
}
else
{
lean_object* v___x_63_; 
lean_dec(v_fst_46_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v___x_55_);
lean_ctor_set(v___x_49_, 0, v_fst_33_);
v___x_63_ = v___x_49_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_fst_33_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_55_);
v___x_63_ = v_reuseFailAlloc_67_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_65_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_63_);
v___x_65_ = v___x_43_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
}
else
{
lean_object* v___x_76_; 
lean_dec(v_a_41_);
if (v_isShared_37_ == 0)
{
v___x_76_ = v___x_36_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_fst_33_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_snd_34_);
v___x_76_ = v_reuseFailAlloc_80_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_78_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_76_);
v___x_78_ = v___x_43_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_del_object(v___x_36_);
lean_dec(v_snd_34_);
lean_dec(v_fst_33_);
v_a_82_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_40_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_40_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___boxed(lean_object* v_id_91_, lean_object* v_a_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_91_, v_a_92_);
lean_dec_ref(v_id_91_);
return v_res_94_;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__0(void){
_start:
{
lean_object* v___x_95_; uint64_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(2147483648u);
v___x_96_ = lean_int64_of_nat(v___x_95_);
return v___x_96_;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__1(void){
_start:
{
uint64_t v___x_97_; uint64_t v_start_98_; 
v___x_97_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__0, &l_Std_Time_Database_Windows_getZoneRules___closed__0_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__0);
v_start_98_ = lean_int64_neg(v___x_97_);
return v_start_98_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1(void){
_start:
{
uint64_t v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_102_ = lean_box_uint64(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3(void){
_start:
{
lean_object* v_transitions_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_transitions_103_ = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__2));
v___x_104_ = l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_transitions_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__4));
v___x_108_ = lean_mk_io_user_error(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* v_id_109_){
_start:
{
uint64_t v_start_111_; uint8_t v___x_112_; lean_object* v___x_113_; 
v_start_111_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_112_ = 1;
v___x_113_ = lean_windows_get_next_transition(v_id_109_, v_start_111_, v___x_112_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_146_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_146_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_146_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_146_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
if (lean_obj_tag(v_a_114_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
lean_del_object(v___x_116_);
v_val_118_ = lean_ctor_get(v_a_114_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v_a_114_, 1);
v___x_119_ = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__3, &l_Std_Time_Database_Windows_getZoneRules___closed__3_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__3);
v___x_120_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_109_, v___x_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_133_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_133_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_snd_125_; lean_object* v_snd_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v_snd_125_ = lean_ctor_get(v_val_118_, 1);
lean_inc(v_snd_125_);
lean_dec(v_val_118_);
v_snd_126_ = lean_ctor_get(v_a_121_, 1);
lean_inc(v_snd_126_);
lean_dec(v_a_121_);
v___x_127_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_125_);
lean_dec(v_snd_125_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v_snd_126_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_131_ = v___x_123_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_val_118_);
v_a_134_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_120_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_120_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec(v_a_114_);
v___x_142_ = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__5, &l_Std_Time_Database_Windows_getZoneRules___closed__5_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__5);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
lean_ctor_set(v___x_116_, 0, v___x_142_);
v___x_144_ = v___x_116_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_113_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_113_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* v_id_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_Database_Windows_getZoneRules(v_id_155_);
lean_dec_ref(v_id_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_nat_to_int(v_a_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_nat_to_int(v_a_160_);
v___x_162_ = l_Rat_ofInt(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object* v_id_163_, lean_object* v_inst_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_163_, v_a_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object* v_id_168_, lean_object* v_inst_169_, lean_object* v_a_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(v_id_168_, v_inst_169_, v_a_170_);
lean_dec_ref(v_id_168_);
return v_res_172_;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_default(void){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object* v_x_174_, lean_object* v_id_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_Time_Database_Windows_getZoneRules(v_id_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object* v_x_178_, lean_object* v_id_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Time_Database_WindowsDb_inst___lam__0(v_x_178_, v_id_179_);
lean_dec_ref(v_id_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object* v_x_182_){
_start:
{
uint64_t v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_185_ = lean_get_windows_local_timezone_id_at(v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = l_Std_Time_Database_Windows_getZoneRules(v_a_186_);
lean_dec(v_a_186_);
return v___x_187_;
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_185_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_185_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object* v_x_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_Database_WindowsDb_inst___lam__1(v_x_196_);
return v_res_198_;
}
}
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1 = _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1();
lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1);
l_Std_Time_Database_WindowsDb_default = _init_l_Std_Time_Database_WindowsDb_default();
lean_mark_persistent(l_Std_Time_Database_WindowsDb_default);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_Windows(builtin);
}
#ifdef __cplusplus
}
#endif
