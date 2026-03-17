// Lean compiler output
// Module: Lean.LoadDynlib
// Imports: public import Init.System.IO import Init.Data.String.TakeDrop import Init.Data.ToString.Macro
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object*);
lean_object* lean_dynlib_load(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object*, lean_object*);
lean_object* lean_dynlib_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_dynlib_symbol_run_as_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_shared"};
static const lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object*);
static const lean_string_object l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_loadPlugin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialize_"};
static const lean_object* l_Lean_loadPlugin___closed__0 = (const lean_object*)&l_Lean_loadPlugin___closed__0_value;
static const lean_string_object l_Lean_loadPlugin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "error loading plugin, initializer not found '"};
static const lean_object* l_Lean_loadPlugin___closed__1 = (const lean_object*)&l_Lean_loadPlugin___closed__1_value;
static const lean_string_object l_Lean_loadPlugin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_loadPlugin___closed__2 = (const lean_object*)&l_Lean_loadPlugin___closed__2_value;
static const lean_string_object l_Lean_loadPlugin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "error, plugin has invalid file name '"};
static const lean_object* l_Lean_loadPlugin___closed__3 = (const lean_object*)&l_Lean_loadPlugin___closed__3_value;
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object* v_dynlib_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object* v_dynlib_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(v_dynlib_4_);
lean_dec(v_dynlib_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object* v_path_8_, lean_object* v_a_00___x40___internal___hyg_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lean_dynlib_load(v_path_8_);
lean_dec_ref(v_path_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object* v_dynlib_13_, lean_object* v_sym_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_dynlib_get(v_dynlib_13_, v_sym_14_);
lean_dec_ref(v_sym_14_);
lean_dec(v_dynlib_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object* v_dynlib_19_, lean_object* v_sym_20_, lean_object* v_a_00___x40___internal___hyg_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lean_dynlib_symbol_run_as_init(v_dynlib_19_, v_sym_20_);
lean_dec(v_sym_20_);
lean_dec(v_dynlib_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object* v_dynlib_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_runtime_mark_persistent(v_dynlib_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object* v_dynlib_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(v_dynlib_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object* v_path_29_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_dynlib_load(v_path_29_);
lean_dec_ref(v_path_29_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_41_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_41_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_41_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_41_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_36_ = lean_runtime_mark_persistent(v_a_32_);
lean_dec(v___x_36_);
v___x_37_ = lean_box(0);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_37_);
v___x_39_ = v___x_34_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_a_42_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_31_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_31_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object* v_path_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lean_load_dynlib(v_path_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(lean_object* v_dynlib_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_runtime_mark_persistent(v_dynlib_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1___boxed(lean_object* v_dynlib_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__1(v_dynlib_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object* v_dynlib_59_, lean_object* v_sym_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_dynlib_symbol_run_as_init(v_dynlib_59_, v_sym_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object* v_dynlib_63_, lean_object* v_sym_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(v_dynlib_63_, v_sym_64_);
lean_dec(v_sym_64_);
lean_dec(v_dynlib_63_);
return v_res_66_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
v___x_69_ = lean_string_utf8_byte_size(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object* v_s_70_){
_start:
{
lean_object* v_str_71_; lean_object* v_startInclusive_72_; lean_object* v_endExclusive_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_str_71_ = lean_ctor_get(v_s_70_, 0);
v_startInclusive_72_ = lean_ctor_get(v_s_70_, 1);
v_endExclusive_73_ = lean_ctor_get(v_s_70_, 2);
v___x_74_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
v___x_75_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1, &l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1);
v___x_76_ = lean_nat_sub(v_endExclusive_73_, v_startInclusive_72_);
v___x_77_ = lean_nat_dec_le(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec(v___x_76_);
return v_s_70_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_nat_sub(v___x_76_, v___x_75_);
lean_dec(v___x_76_);
v___x_80_ = lean_nat_add(v_startInclusive_72_, v___x_79_);
v___x_81_ = lean_string_memcmp(v_str_71_, v___x_74_, v___x_80_, v___x_78_, v___x_75_);
lean_dec(v___x_80_);
if (v___x_81_ == 0)
{
lean_dec(v___x_79_);
return v_s_70_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
lean_inc(v_startInclusive_72_);
lean_inc_ref(v_str_71_);
v___x_82_ = l_String_Slice_pos_x21(v_s_70_, v___x_79_);
lean_dec(v___x_79_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_s_70_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; 
v_unused_91_ = lean_ctor_get(v_s_70_, 2);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_s_70_, 1);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_s_70_, 0);
lean_dec(v_unused_93_);
v___x_84_ = v_s_70_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_dec(v_s_70_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_nat_add(v_startInclusive_72_, v___x_82_);
lean_dec(v___x_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 2, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_str_71_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_startInclusive_72_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v___x_86_);
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
static lean_object* _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_96_ = lean_string_utf8_byte_size(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object* v_s_97_){
_start:
{
lean_object* v_str_98_; lean_object* v_startInclusive_99_; lean_object* v_endExclusive_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_str_98_ = lean_ctor_get(v_s_97_, 0);
v_startInclusive_99_ = lean_ctor_get(v_s_97_, 1);
v_endExclusive_100_ = lean_ctor_get(v_s_97_, 2);
v___x_101_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_102_ = lean_obj_once(&l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1);
v___x_103_ = lean_nat_sub(v_endExclusive_100_, v_startInclusive_99_);
v___x_104_ = lean_nat_dec_le(v___x_102_, v___x_103_);
lean_dec(v___x_103_);
if (v___x_104_ == 0)
{
return v_s_97_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_string_memcmp(v_str_98_, v___x_101_, v_startInclusive_99_, v___x_105_, v___x_102_);
if (v___x_106_ == 0)
{
return v_s_97_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
lean_inc(v_endExclusive_100_);
lean_inc(v_startInclusive_99_);
lean_inc_ref(v_str_98_);
v___x_107_ = l_String_Slice_pos_x21(v_s_97_, v___x_102_);
v_isSharedCheck_115_ = !lean_is_exclusive(v_s_97_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; lean_object* v_unused_117_; lean_object* v_unused_118_; 
v_unused_116_ = lean_ctor_get(v_s_97_, 2);
lean_dec(v_unused_116_);
v_unused_117_ = lean_ctor_get(v_s_97_, 1);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_s_97_, 0);
lean_dec(v_unused_118_);
v___x_109_ = v_s_97_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_s_97_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_nat_add(v_startInclusive_99_, v___x_107_);
lean_dec(v___x_107_);
lean_dec(v_startInclusive_99_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_str_98_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_endExclusive_100_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object* v_s_119_, lean_object* v_pat_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_string_utf8_byte_size(v_s_119_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_s_119_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
v___x_124_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object* v_s_125_, lean_object* v_pat_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_s_125_, v_pat_126_);
lean_dec_ref(v_pat_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lean_load_plugin(lean_object* v_path_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_io_realpath(v_path_132_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_181_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_181_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_181_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_181_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; 
lean_inc(v_a_135_);
v___x_139_ = l_System_FilePath_fileStem(v_a_135_);
if (lean_obj_tag(v___x_139_) == 1)
{
lean_object* v_val_140_; lean_object* v___x_141_; 
lean_del_object(v___x_137_);
v_val_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v___x_139_);
v___x_141_ = lean_dynlib_load(v_a_135_);
lean_dec(v_a_135_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_164_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_164_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_164_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_164_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_146_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_147_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_val_140_, v___x_146_);
v___x_148_ = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(v___x_147_);
v___x_149_ = ((lean_object*)(l_Lean_loadPlugin___closed__0));
v___x_150_ = l_String_Slice_toString(v___x_148_);
lean_dec_ref(v___x_148_);
v___x_151_ = lean_string_append(v___x_149_, v___x_150_);
lean_dec_ref(v___x_150_);
v___x_152_ = lean_dynlib_get(v_a_142_, v___x_151_);
if (lean_obj_tag(v___x_152_) == 1)
{
lean_object* v_val_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v___x_151_);
lean_del_object(v___x_144_);
v_val_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_val_153_);
lean_dec_ref(v___x_152_);
lean_inc(v_a_142_);
v___x_154_ = lean_runtime_mark_persistent(v_a_142_);
lean_dec(v___x_154_);
v___x_155_ = lean_dynlib_symbol_run_as_init(v_a_142_, v_val_153_);
lean_dec(v_val_153_);
lean_dec(v_a_142_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_dec(v___x_152_);
lean_dec(v_a_142_);
v___x_156_ = ((lean_object*)(l_Lean_loadPlugin___closed__1));
v___x_157_ = lean_string_append(v___x_156_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_158_ = ((lean_object*)(l_Lean_loadPlugin___closed__2));
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
v___x_160_ = lean_mk_io_user_error(v___x_159_);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 1);
lean_ctor_set(v___x_144_, 0, v___x_160_);
v___x_162_ = v___x_144_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_val_140_);
v_a_165_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_141_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_141_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
lean_dec(v___x_139_);
v___x_173_ = ((lean_object*)(l_Lean_loadPlugin___closed__3));
v___x_174_ = lean_string_append(v___x_173_, v_a_135_);
lean_dec(v_a_135_);
v___x_175_ = ((lean_object*)(l_Lean_loadPlugin___closed__2));
v___x_176_ = lean_string_append(v___x_174_, v___x_175_);
v___x_177_ = lean_mk_io_user_error(v___x_176_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
lean_ctor_set(v___x_137_, 0, v___x_177_);
v___x_179_ = v___x_137_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_182_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_134_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_134_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object* v_path_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lean_load_plugin(v_path_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object* v_pat_193_, lean_object* v_s_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v_s_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object* v_pat_196_, lean_object* v_s_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(v_pat_196_, v_s_197_);
lean_dec_ref(v_pat_196_);
return v_res_198_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_LoadDynlib_0__Lean_DynlibImpl = _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LoadDynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LoadDynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LoadDynlib(builtin);
}
#ifdef __cplusplus
}
#endif
