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
uint64_t lean_int64_of_nat(lean_object*);
uint64_t lean_int64_neg(uint64_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_windows_get_next_transition(lean_object*, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object*);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object*);
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
static uint64_t _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0(void){
_start:
{
lean_object* v___x_28_; uint64_t v___x_29_; 
v___x_28_ = lean_cstr_to_nat("32503690800");
v___x_29_ = lean_int64_of_nat(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object* v_id_30_, lean_object* v_b_31_){
_start:
{
lean_object* v_fst_33_; lean_object* v_snd_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_89_; 
v_fst_33_ = lean_ctor_get(v_b_31_, 0);
v_snd_34_ = lean_ctor_get(v_b_31_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_b_31_);
if (v_isSharedCheck_89_ == 0)
{
v___x_36_ = v_b_31_;
v_isShared_37_ = v_isSharedCheck_89_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_snd_34_);
lean_inc(v_fst_33_);
lean_dec(v_b_31_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_89_;
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
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_80_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_80_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_80_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_80_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
if (lean_obj_tag(v_a_41_) == 1)
{
lean_object* v_val_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_73_; 
v_val_45_ = lean_ctor_get(v_a_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref(v_a_41_);
v_fst_46_ = lean_ctor_get(v_val_45_, 0);
v_snd_47_ = lean_ctor_get(v_val_45_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_val_45_);
if (v_isSharedCheck_73_ == 0)
{
v___x_49_ = v_val_45_;
v_isShared_50_ = v_isSharedCheck_73_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_snd_47_);
lean_inc(v_fst_46_);
lean_dec(v_val_45_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_73_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
uint64_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint64_t v___x_63_; uint64_t v___x_64_; uint8_t v___x_65_; 
v___x_51_ = lean_unbox_uint64(v_fst_33_);
v___x_52_ = lean_int64_to_int_sint(v___x_51_);
v___x_53_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_47_);
lean_dec(v_snd_47_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_array_push(v_snd_34_, v___x_54_);
v___x_63_ = lean_unbox_uint64(v_fst_46_);
v___x_64_ = lean_unbox_uint64(v_fst_33_);
v___x_65_ = lean_int64_dec_le(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
uint64_t v___x_66_; uint64_t v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_uint64_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___closed__0);
v___x_67_ = lean_unbox_uint64(v_fst_46_);
v___x_68_ = lean_int64_dec_le(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
lean_del_object(v___x_49_);
lean_del_object(v___x_43_);
lean_dec(v_fst_33_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_55_);
lean_ctor_set(v___x_36_, 0, v_fst_46_);
v___x_70_ = v___x_36_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_fst_46_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_55_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v_b_31_ = v___x_70_;
goto _start;
}
}
else
{
lean_dec(v_fst_46_);
lean_del_object(v___x_36_);
goto v___jp_56_;
}
}
else
{
lean_dec(v_fst_46_);
lean_del_object(v___x_36_);
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v___x_58_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v___x_55_);
lean_ctor_set(v___x_49_, 0, v_fst_33_);
v___x_58_ = v___x_49_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_fst_33_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_55_);
v___x_58_ = v_reuseFailAlloc_62_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_60_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_58_);
v___x_60_ = v___x_43_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
else
{
lean_object* v___x_75_; 
lean_dec(v_a_41_);
if (v_isShared_37_ == 0)
{
v___x_75_ = v___x_36_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_fst_33_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_snd_34_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_77_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_75_);
v___x_77_ = v___x_43_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_del_object(v___x_36_);
lean_dec(v_snd_34_);
lean_dec(v_fst_33_);
v_a_81_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_40_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_40_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object* v_id_90_, lean_object* v_b_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(v_id_90_, v_b_91_);
lean_dec_ref(v_id_90_);
return v_res_93_;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__0(void){
_start:
{
lean_object* v___x_94_; uint64_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(2147483648u);
v___x_95_ = lean_int64_of_nat(v___x_94_);
return v___x_95_;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__1(void){
_start:
{
uint64_t v___x_96_; uint64_t v_start_97_; 
v___x_96_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__0, &l_Std_Time_Database_Windows_getZoneRules___closed__0_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__0);
v_start_97_ = lean_int64_neg(v___x_96_);
return v_start_97_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1(void){
_start:
{
uint64_t v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_101_ = lean_box_uint64(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3(void){
_start:
{
lean_object* v_transitions_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_transitions_102_ = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__2));
v___x_103_ = l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_transitions_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__4));
v___x_107_ = lean_mk_io_user_error(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* v_id_108_){
_start:
{
uint64_t v_start_110_; uint8_t v___x_111_; lean_object* v___x_112_; 
v_start_110_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_111_ = 1;
v___x_112_ = lean_windows_get_next_transition(v_id_108_, v_start_110_, v___x_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_151_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_151_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_151_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_151_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
if (lean_obj_tag(v_a_113_) == 1)
{
lean_object* v_val_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_115_);
v_val_117_ = lean_ctor_get(v_a_113_, 0);
lean_inc(v_val_117_);
lean_dec_ref(v_a_113_);
v___x_118_ = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__3, &l_Std_Time_Database_Windows_getZoneRules___closed__3_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__3);
v___x_119_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Time_Database_Windows_getZoneRules_spec__1(v_id_108_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_138_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_138_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_138_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_138_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_snd_124_; lean_object* v_snd_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_136_; 
v_snd_124_ = lean_ctor_get(v_val_117_, 1);
lean_inc(v_snd_124_);
lean_dec(v_val_117_);
v_snd_125_ = lean_ctor_get(v_a_120_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_120_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_a_120_, 0);
lean_dec(v_unused_137_);
v___x_127_ = v_a_120_;
v_isShared_128_ = v_isSharedCheck_136_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snd_125_);
lean_dec(v_a_120_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_136_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_124_);
lean_dec(v_snd_124_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_snd_125_);
v___x_131_ = v_reuseFailAlloc_135_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_131_);
v___x_133_ = v___x_122_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_val_117_);
v_a_139_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_119_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_119_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
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
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_a_113_);
v___x_147_ = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__5, &l_Std_Time_Database_Windows_getZoneRules___closed__5_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__5);
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 1);
lean_ctor_set(v___x_115_, 0, v___x_147_);
v___x_149_ = v___x_115_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_112_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_112_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* v_id_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Time_Database_Windows_getZoneRules(v_id_160_);
lean_dec_ref(v_id_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_nat_to_int(v_a_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_nat_to_int(v_a_165_);
v___x_167_ = l_Rat_ofInt(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_toCtorIdx(lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_unsigned_to_nat(0u);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_default(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object* v_x_171_, lean_object* v_id_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Time_Database_Windows_getZoneRules(v_id_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object* v_x_175_, lean_object* v_id_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_Database_WindowsDb_inst___lam__0(v_x_175_, v_id_176_);
lean_dec_ref(v_id_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object* v_x_179_){
_start:
{
uint64_t v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_182_ = lean_get_windows_local_timezone_id_at(v___x_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref(v___x_182_);
v___x_184_ = l_Std_Time_Database_Windows_getZoneRules(v_a_183_);
lean_dec(v_a_183_);
return v___x_184_;
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_182_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_182_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object* v_x_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Time_Database_WindowsDb_inst___lam__1(v_x_193_);
return v_res_195_;
}
}
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
