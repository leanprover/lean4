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
LEAN_EXPORT void l_Std_Time_Database_Windows_getNextTransition_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
uint64_t v_a_00___x40___internal___hyg_2_ = stack[1].m_num;
uint8_t v_a_00___x40___internal___hyg_3_ = stack[2].m_num;
lean_object* v_res_5_;
v_res_5_ = lean_windows_get_next_transition(v_a_00___x40___internal___hyg_1_, v_a_00___x40___internal___hyg_2_, v_a_00___x40___internal___hyg_3_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getNextTransition___boxed(lean_object* v_a_00___x40___internal___hyg_6_, lean_object* v_a_00___x40___internal___hyg_7_, lean_object* v_a_00___x40___internal___hyg_8_, lean_object* v_a_00___x40___internal___hyg_9_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_2__boxed_10_; uint8_t v_a_00___x40___internal___hyg_3__boxed_11_; lean_object* v_res_12_; 
v_a_00___x40___internal___hyg_2__boxed_10_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_7_);
lean_dec_ref(v_a_00___x40___internal___hyg_7_);
v_a_00___x40___internal___hyg_3__boxed_11_ = lean_unbox(v_a_00___x40___internal___hyg_8_);
v_res_12_ = lean_windows_get_next_transition(v_a_00___x40___internal___hyg_6_, v_a_00___x40___internal___hyg_2__boxed_10_, v_a_00___x40___internal___hyg_3__boxed_11_);
lean_dec_ref(v_a_00___x40___internal___hyg_6_);
return v_res_12_;
}
}
LEAN_EXPORT void l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_00___x40___internal___hyg_13_ = stack[0].m_num;
lean_object* v_res_15_;
v_res_15_ = lean_get_windows_local_timezone_id_at(v_a_00___x40___internal___hyg_13_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(lean_object* v_a_00___x40___internal___hyg_16_, lean_object* v_a_00___x40___internal___hyg_17_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_1__boxed_18_; lean_object* v_res_19_; 
v_a_00___x40___internal___hyg_1__boxed_18_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_16_);
lean_dec_ref(v_a_00___x40___internal___hyg_16_);
v_res_19_ = lean_get_windows_local_timezone_id_at(v_a_00___x40___internal___hyg_1__boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(lean_object* v_res_20_){
_start:
{
lean_object* v_offset_21_; lean_object* v_name_22_; lean_object* v_abbreviation_23_; uint8_t v_isDST_24_; uint8_t v___x_25_; uint8_t v___x_26_; lean_object* v___x_27_; 
v_offset_21_ = lean_ctor_get(v_res_20_, 0);
v_name_22_ = lean_ctor_get(v_res_20_, 1);
v_abbreviation_23_ = lean_ctor_get(v_res_20_, 2);
v_isDST_24_ = lean_ctor_get_uint8(v_res_20_, sizeof(void*)*3);
v___x_25_ = 0;
v___x_26_ = 1;
lean_inc_ref(v_name_22_);
lean_inc_ref(v_abbreviation_23_);
lean_inc(v_offset_21_);
v___x_27_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_27_, 0, v_offset_21_);
lean_ctor_set(v___x_27_, 1, v_abbreviation_23_);
lean_ctor_set(v___x_27_, 2, v_name_22_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*3, v_isDST_24_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*3 + 1, v___x_25_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*3 + 2, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(lean_object* v_res_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_res_28_);
lean_dec_ref(v_res_28_);
return v_res_29_;
}
}
static uint64_t _init_l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_30_; uint64_t v___x_31_; 
v___x_30_ = lean_cstr_to_nat("32503690800");
v___x_31_ = lean_int64_of_nat(v___x_30_);
return v___x_31_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(lean_object* v_id_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_fst_35_; lean_object* v_snd_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_91_; 
v_fst_35_ = lean_ctor_get(v_a_33_, 0);
v_snd_36_ = lean_ctor_get(v_a_33_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_a_33_);
if (v_isSharedCheck_91_ == 0)
{
v___x_38_ = v_a_33_;
v_isShared_39_ = v_isSharedCheck_91_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_snd_36_);
lean_inc(v_fst_35_);
lean_dec(v_a_33_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_91_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
uint8_t v___x_40_; uint64_t v___x_41_; lean_object* v___x_42_; 
v___x_40_ = 0;
v___x_41_ = lean_unbox_uint64(v_fst_35_);
v___x_42_ = lean_windows_get_next_transition(v_id_32_, v___x_41_, v___x_40_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_82_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_82_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_82_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_82_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
if (lean_obj_tag(v_a_43_) == 1)
{
lean_object* v_val_47_; lean_object* v_fst_48_; lean_object* v_snd_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_75_; 
v_val_47_ = lean_ctor_get(v_a_43_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v_a_43_, 1);
v_fst_48_ = lean_ctor_get(v_val_47_, 0);
v_snd_49_ = lean_ctor_get(v_val_47_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_val_47_);
if (v_isSharedCheck_75_ == 0)
{
v___x_51_ = v_val_47_;
v_isShared_52_ = v_isSharedCheck_75_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_snd_49_);
lean_inc(v_fst_48_);
lean_dec(v_val_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_75_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint64_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint64_t v___x_65_; uint64_t v___x_66_; uint8_t v___x_67_; 
v___x_53_ = lean_unbox_uint64(v_fst_35_);
v___x_54_ = lean_int64_to_int_sint(v___x_53_);
v___x_55_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_49_);
lean_dec(v_snd_49_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_array_push(v_snd_36_, v___x_56_);
v___x_65_ = lean_unbox_uint64(v_fst_48_);
v___x_66_ = lean_unbox_uint64(v_fst_35_);
v___x_67_ = lean_int64_dec_le(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
uint64_t v___x_68_; uint64_t v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_uint64_once(&l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0);
v___x_69_ = lean_unbox_uint64(v_fst_48_);
v___x_70_ = lean_int64_dec_le(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_72_; 
lean_del_object(v___x_51_);
lean_del_object(v___x_45_);
lean_dec(v_fst_35_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v___x_57_);
lean_ctor_set(v___x_38_, 0, v_fst_48_);
v___x_72_ = v___x_38_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_fst_48_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_57_);
v___x_72_ = v_reuseFailAlloc_74_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
v_a_33_ = v___x_72_;
goto _start;
}
}
else
{
lean_dec(v_fst_48_);
lean_del_object(v___x_38_);
goto v___jp_58_;
}
}
else
{
lean_dec(v_fst_48_);
lean_del_object(v___x_38_);
goto v___jp_58_;
}
v___jp_58_:
{
lean_object* v___x_60_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_57_);
lean_ctor_set(v___x_51_, 0, v_fst_35_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_fst_35_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_57_);
v___x_60_ = v_reuseFailAlloc_64_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_62_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_60_);
v___x_62_ = v___x_45_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
else
{
lean_object* v___x_77_; 
lean_dec(v_a_43_);
if (v_isShared_39_ == 0)
{
v___x_77_ = v___x_38_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_fst_35_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_snd_36_);
v___x_77_ = v_reuseFailAlloc_81_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_79_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_77_);
v___x_79_ = v___x_45_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_del_object(v___x_38_);
lean_dec(v_snd_36_);
lean_dec(v_fst_35_);
v_a_83_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_42_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_42_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_32_ = stack[0].m_obj;
lean_object* v_a_33_ = stack[1].m_obj;
lean_object* v_res_92_;
v_res_92_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_32_, v_a_33_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___boxed(lean_object* v_id_93_, lean_object* v_a_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_93_, v_a_94_);
lean_dec_ref(v_id_93_);
return v_res_96_;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__0(void){
_start:
{
lean_object* v___x_97_; uint64_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(2147483648u);
v___x_98_ = lean_int64_of_nat(v___x_97_);
return v___x_98_;
}
}
static uint64_t _init_l_Std_Time_Database_Windows_getZoneRules___closed__1(void){
_start:
{
uint64_t v___x_99_; uint64_t v_start_100_; 
v___x_99_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__0, &l_Std_Time_Database_Windows_getZoneRules___closed__0_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__0);
v_start_100_ = lean_int64_neg(v___x_99_);
return v_start_100_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1(void){
_start:
{
uint64_t v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_104_ = lean_box_uint64(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__3(void){
_start:
{
lean_object* v_transitions_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_transitions_105_ = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__2));
v___x_106_ = l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_transitions_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Std_Time_Database_Windows_getZoneRules___closed__5(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Std_Time_Database_Windows_getZoneRules___closed__4));
v___x_110_ = lean_mk_io_user_error(v___x_109_);
return v___x_110_;
}
}
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object* v_id_111_){
_start:
{
uint64_t v_start_113_; uint8_t v___x_114_; lean_object* v___x_115_; 
v_start_113_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_114_ = 1;
v___x_115_ = lean_windows_get_next_transition(v_id_111_, v_start_113_, v___x_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_148_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_148_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_148_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_148_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
if (lean_obj_tag(v_a_116_) == 1)
{
lean_object* v_val_120_; lean_object* v_snd_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_del_object(v___x_118_);
v_val_120_ = lean_ctor_get(v_a_116_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_a_116_, 1);
v_snd_121_ = lean_ctor_get(v_val_120_, 1);
lean_inc(v_snd_121_);
lean_dec(v_val_120_);
v___x_122_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_121_);
lean_dec(v_snd_121_);
v___x_123_ = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__3, &l_Std_Time_Database_Windows_getZoneRules___closed__3_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__3);
v___x_124_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_111_, v___x_123_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_snd_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_snd_129_ = lean_ctor_get(v_a_125_, 1);
lean_inc(v_snd_129_);
lean_dec(v_a_125_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v___x_122_);
lean_ctor_set(v___x_131_, 1, v_snd_129_);
lean_ctor_set(v___x_131_, 2, v___x_130_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_131_);
v___x_133_ = v___x_127_;
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
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v___x_122_);
v_a_136_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_124_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_124_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
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
lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_a_116_);
v___x_144_ = lean_obj_once(&l_Std_Time_Database_Windows_getZoneRules___closed__5, &l_Std_Time_Database_Windows_getZoneRules___closed__5_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__5);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
lean_ctor_set(v___x_118_, 0, v___x_144_);
v___x_146_ = v___x_118_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_115_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_115_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_Windows_getZoneRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_111_ = stack[0].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Std_Time_Database_Windows_getZoneRules(v_id_111_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_Windows_getZoneRules___boxed(lean_object* v_id_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Time_Database_Windows_getZoneRules(v_id_158_);
lean_dec_ref(v_id_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_nat_to_int(v_a_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_nat_to_int(v_a_163_);
v___x_165_ = l_Rat_ofInt(v___x_164_);
return v___x_165_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(lean_object* v_id_166_, lean_object* v_inst_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_166_, v_a_168_);
return v___x_170_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_166_ = stack[0].m_obj;
lean_object* v_a_168_ = stack[2].m_obj;
lean_object* v_res_171_;
v_res_171_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(v_id_166_, lean_box(0), v_a_168_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(lean_object* v_id_172_, lean_object* v_inst_173_, lean_object* v_a_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Init_While_0__repeatM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(v_id_172_, v_inst_173_, v_a_174_);
lean_dec_ref(v_id_172_);
return v_res_176_;
}
}
static lean_object* _init_l_Std_Time_Database_WindowsDb_default(void){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_box(0);
return v___x_177_;
}
}
lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0(lean_object* v_x_178_, lean_object* v_id_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_Time_Database_Windows_getZoneRules(v_id_179_);
return v___x_181_;
}
}
LEAN_EXPORT void l_Std_Time_Database_WindowsDb_inst___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_178_ = stack[0].m_obj;
lean_object* v_id_179_ = stack[1].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_Std_Time_Database_WindowsDb_inst___lam__0(v_x_178_, v_id_179_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(lean_object* v_x_183_, lean_object* v_id_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Time_Database_WindowsDb_inst___lam__0(v_x_183_, v_id_184_);
lean_dec_ref(v_id_184_);
return v_res_186_;
}
}
lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1(lean_object* v_x_187_){
_start:
{
uint64_t v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_uint64_once(&l_Std_Time_Database_Windows_getZoneRules___closed__1, &l_Std_Time_Database_Windows_getZoneRules___closed__1_once, _init_l_Std_Time_Database_Windows_getZoneRules___closed__1);
v___x_190_ = lean_get_windows_local_timezone_id_at(v___x_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = l_Std_Time_Database_Windows_getZoneRules(v_a_191_);
lean_dec(v_a_191_);
return v___x_192_;
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_a_193_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_190_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_190_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Database_WindowsDb_inst___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_187_ = stack[0].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Std_Time_Database_WindowsDb_inst___lam__1(v_x_187_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(lean_object* v_x_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Time_Database_WindowsDb_inst___lam__1(v_x_202_);
return v_res_204_;
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
