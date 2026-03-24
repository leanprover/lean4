// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: public import Std.Time.Zoned.ZonedDateTime public import Std.Time.Zoned.Database.Basic public import Std.Time.Zoned.Database.TZdb public import Std.Time.Zoned.Database.Windows import Init.System.Platform
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
lean_object* lean_array_push(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_io_getenv(lean_object*);
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_System_FilePath_pathExists(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*);
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TZDIR"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__0 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__0_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/usr/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__1 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__1_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "/share/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__2 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__2_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/etc/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__3 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__3_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "/usr/share/lib/zoneinfo"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__4 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__4_value;
static const lean_array_object l_Std_Time_Database_defaultGetZoneRules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__1_value),((lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__2_value),((lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__3_value),((lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__4_value)}};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__5 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__5_value;
static lean_once_cell_t l_Std_Time_Database_defaultGetZoneRules___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Std_Time_Database_defaultGetZoneRules___closed__6;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cannot find "};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__7 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__7_value;
static const lean_string_object l_Std_Time_Database_defaultGetZoneRules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " in the local timezone database"};
static const lean_object* l_Std_Time_Database_defaultGetZoneRules___closed__8 = (const lean_object*)&l_Std_Time_Database_defaultGetZoneRules___closed__8_value;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "/etc/localtime"};
static const lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___closed__0 = (const lean_object*)&l_Std_Time_Database_defaultGetLocalZoneRules___closed__0_value;
static lean_once_cell_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__1;
static lean_once_cell_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_Time_Database_defaultGetLocalZoneRules___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules();
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(lean_object* v_a_4_, lean_object* v_as_5_, size_t v_sz_6_, size_t v_i_7_, lean_object* v_b_8_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_lt(v_i_7_, v_sz_6_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec_ref(v_a_4_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v_b_8_);
return v___x_11_;
}
else
{
lean_object* v_a_12_; uint8_t v___x_13_; lean_object* v___x_14_; 
lean_dec_ref(v_b_8_);
v_a_12_ = lean_array_uget_borrowed(v_as_5_, v_i_7_);
v___x_13_ = l_System_FilePath_pathExists(v_a_12_);
v___x_14_ = lean_box(0);
if (v___x_13_ == 0)
{
lean_object* v___x_15_; size_t v___x_16_; size_t v___x_17_; 
v___x_15_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0));
v___x_16_ = ((size_t)1ULL);
v___x_17_ = lean_usize_add(v_i_7_, v___x_16_);
v_i_7_ = v___x_17_;
v_b_8_ = v___x_15_;
goto _start;
}
else
{
lean_object* v___x_19_; 
lean_inc(v_a_12_);
v___x_19_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_12_, v_a_4_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_29_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_29_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_29_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_29_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v_a_20_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_14_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_25_);
v___x_27_ = v___x_22_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_19_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_19_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object* v_a_38_, lean_object* v_as_39_, lean_object* v_sz_40_, lean_object* v_i_41_, lean_object* v_b_42_, lean_object* v___y_43_){
_start:
{
size_t v_sz_boxed_44_; size_t v_i_boxed_45_; lean_object* v_res_46_; 
v_sz_boxed_44_ = lean_unbox_usize(v_sz_40_);
lean_dec(v_sz_40_);
v_i_boxed_45_ = lean_unbox_usize(v_i_41_);
lean_dec(v_i_41_);
v_res_46_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(v_a_38_, v_as_39_, v_sz_boxed_44_, v_i_boxed_45_, v_b_42_);
lean_dec_ref(v_as_39_);
return v_res_46_;
}
}
static size_t _init_l_Std_Time_Database_defaultGetZoneRules___closed__6(void){
_start:
{
lean_object* v___x_62_; size_t v_sz_63_; 
v___x_62_ = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__5));
v_sz_63_ = lean_array_size(v___x_62_);
return v_sz_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object* v_a_66_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = l_System_Platform_isWindows;
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__0));
v___x_70_ = lean_io_getenv(v___x_69_);
if (lean_obj_tag(v___x_70_) == 1)
{
lean_object* v_val_71_; lean_object* v___x_72_; 
v_val_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v___x_70_);
v___x_72_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_val_71_, v_a_66_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; size_t v_sz_75_; size_t v___x_76_; lean_object* v___x_77_; 
lean_dec(v___x_70_);
v___x_73_ = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__5));
v___x_74_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0___closed__0));
v_sz_75_ = lean_usize_once(&l_Std_Time_Database_defaultGetZoneRules___closed__6, &l_Std_Time_Database_defaultGetZoneRules___closed__6_once, _init_l_Std_Time_Database_defaultGetZoneRules___closed__6);
v___x_76_ = ((size_t)0ULL);
lean_inc_ref(v_a_66_);
v___x_77_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_defaultGetZoneRules_spec__0(v_a_66_, v___x_73_, v_sz_75_, v___x_76_, v___x_74_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_95_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_95_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_95_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_95_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_fst_82_; 
v_fst_82_ = lean_ctor_get(v_a_78_, 0);
lean_inc(v_fst_82_);
lean_dec(v_a_78_);
if (lean_obj_tag(v_fst_82_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_83_ = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__7));
v___x_84_ = lean_string_append(v___x_83_, v_a_66_);
lean_dec_ref(v_a_66_);
v___x_85_ = ((lean_object*)(l_Std_Time_Database_defaultGetZoneRules___closed__8));
v___x_86_ = lean_string_append(v___x_84_, v___x_85_);
v___x_87_ = lean_mk_io_user_error(v___x_86_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 0, v___x_87_);
v___x_89_ = v___x_80_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
else
{
lean_object* v_val_91_; lean_object* v___x_93_; 
lean_dec_ref(v_a_66_);
v_val_91_ = lean_ctor_get(v_fst_82_, 0);
lean_inc(v_val_91_);
lean_dec_ref(v_fst_82_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v_val_91_);
v___x_93_ = v___x_80_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_val_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_a_66_);
v_a_96_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_77_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_77_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Time_Database_Windows_getZoneRules(v_a_66_);
lean_dec_ref(v_a_66_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules___boxed(lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Time_Database_defaultGetZoneRules(v_a_105_);
return v_res_107_;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1(void){
_start:
{
lean_object* v___x_109_; uint64_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(2147483648u);
v___x_110_ = lean_int64_of_nat(v___x_109_);
return v___x_110_;
}
}
static uint64_t _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2(void){
_start:
{
uint64_t v___x_111_; uint64_t v___x_112_; 
v___x_111_ = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__1, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__1_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__1);
v___x_112_ = lean_int64_neg(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_System_Platform_isWindows;
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_Time_Database_defaultGetLocalZoneRules___closed__0));
v___x_116_ = l_Std_Time_Database_TZdb_localRules(v___x_115_);
return v___x_116_;
}
else
{
uint64_t v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_uint64_once(&l_Std_Time_Database_defaultGetLocalZoneRules___closed__2, &l_Std_Time_Database_defaultGetLocalZoneRules___closed__2_once, _init_l_Std_Time_Database_defaultGetLocalZoneRules___closed__2);
v___x_118_ = lean_get_windows_local_timezone_id_at(v___x_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v___x_118_);
v___x_120_ = l_Std_Time_Database_Windows_getZoneRules(v_a_119_);
lean_dec(v_a_119_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_118_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_118_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules___boxed(lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Time_Database_defaultGetLocalZoneRules();
return v_res_130_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TZdb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Windows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database(builtin);
}
#ifdef __cplusplus
}
#endif
