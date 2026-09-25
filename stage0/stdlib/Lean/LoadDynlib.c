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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_DynlibImpl;
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg();
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_loadPlugin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "error loading plugin, initializer not found '"};
static const lean_object* l_Lean_loadPlugin___closed__0 = (const lean_object*)&l_Lean_loadPlugin___closed__0_value;
static const lean_string_object l_Lean_loadPlugin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_loadPlugin___closed__1 = (const lean_object*)&l_Lean_loadPlugin___closed__1_value;
static const lean_string_object l_Lean_loadPlugin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialize_"};
static const lean_object* l_Lean_loadPlugin___closed__2 = (const lean_object*)&l_Lean_loadPlugin___closed__2_value;
static const lean_string_object l_Lean_loadPlugin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "error, plugin has invalid file name '"};
static const lean_object* l_Lean_loadPlugin___closed__3 = (const lean_object*)&l_Lean_loadPlugin___closed__3_value;
LEAN_EXPORT lean_object* lean_load_plugin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object* v_dynlib_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object* v_dynlib_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(v_dynlib_8_);
lean_dec(v_dynlib_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object* v_path_12_, lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lean_dynlib_load(v_path_12_);
lean_dec_ref(v_path_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object* v_dynlib_17_, lean_object* v_sym_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lean_dynlib_get(v_dynlib_17_, v_sym_18_);
lean_dec_ref(v_sym_18_);
lean_dec(v_dynlib_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object* v_dynlib_23_, lean_object* v_sym_24_, lean_object* v_a_00___x40___internal___hyg_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lean_dynlib_symbol_run_as_init(v_dynlib_23_, v_sym_24_);
lean_dec(v_sym_24_);
lean_dec(v_dynlib_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object* v_dynlib_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_runtime_mark_persistent(v_dynlib_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object* v_dynlib_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(v_dynlib_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lean_load_dynlib(lean_object* v_path_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_dynlib_load(v_path_33_);
lean_dec_ref(v_path_33_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_45_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_40_ = lean_runtime_mark_persistent(v_a_36_);
lean_dec(v___x_40_);
v___x_41_ = lean_box(0);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_41_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_35_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_35_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object* v_path_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lean_load_dynlib(v_path_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object* v_dynlib_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_runtime_mark_persistent(v_dynlib_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object* v_dynlib_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(v_dynlib_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7(lean_object* v_dynlib_63_, lean_object* v_sym_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_dynlib_symbol_run_as_init(v_dynlib_63_, v_sym_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7___boxed(lean_object* v_dynlib_67_, lean_object* v_sym_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7(v_dynlib_67_, v_sym_68_);
lean_dec(v_sym_68_);
lean_dec(v_dynlib_67_);
return v_res_70_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
v___x_73_ = lean_string_utf8_byte_size(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object* v_s_74_){
_start:
{
lean_object* v_str_75_; lean_object* v_startInclusive_76_; lean_object* v_endExclusive_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_str_75_ = lean_ctor_get(v_s_74_, 0);
v_startInclusive_76_ = lean_ctor_get(v_s_74_, 1);
v_endExclusive_77_ = lean_ctor_get(v_s_74_, 2);
v___x_78_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
v___x_79_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1, &l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once, _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1);
v___x_80_ = lean_nat_sub(v_endExclusive_77_, v_startInclusive_76_);
v___x_81_ = lean_nat_dec_le(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_dec(v___x_80_);
return v_s_74_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_nat_sub(v___x_80_, v___x_79_);
lean_dec(v___x_80_);
v___x_84_ = lean_nat_add(v_startInclusive_76_, v___x_83_);
v___x_85_ = lean_string_memcmp(v_str_75_, v___x_78_, v___x_84_, v___x_82_, v___x_79_);
lean_dec(v___x_84_);
if (v___x_85_ == 0)
{
lean_dec(v___x_83_);
return v_s_74_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
lean_inc(v_startInclusive_76_);
lean_inc_ref(v_str_75_);
v___x_86_ = l_String_Slice_pos_x21(v_s_74_, v___x_83_);
lean_dec(v___x_83_);
v_isSharedCheck_94_ = !lean_is_exclusive(v_s_74_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; 
v_unused_95_ = lean_ctor_get(v_s_74_, 2);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_s_74_, 1);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_s_74_, 0);
lean_dec(v_unused_97_);
v___x_88_ = v_s_74_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_dec(v_s_74_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_nat_add(v_startInclusive_76_, v___x_86_);
lean_dec(v___x_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_str_75_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_startInclusive_76_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
static lean_object* _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_100_ = lean_string_utf8_byte_size(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object* v_s_101_){
_start:
{
lean_object* v_str_102_; lean_object* v_startInclusive_103_; lean_object* v_endExclusive_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_str_102_ = lean_ctor_get(v_s_101_, 0);
v_startInclusive_103_ = lean_ctor_get(v_s_101_, 1);
v_endExclusive_104_ = lean_ctor_get(v_s_101_, 2);
v___x_105_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_106_ = lean_obj_once(&l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1);
v___x_107_ = lean_nat_sub(v_endExclusive_104_, v_startInclusive_103_);
v___x_108_ = lean_nat_dec_le(v___x_106_, v___x_107_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
return v_s_101_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_string_memcmp(v_str_102_, v___x_105_, v_startInclusive_103_, v___x_109_, v___x_106_);
if (v___x_110_ == 0)
{
return v_s_101_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_119_; 
lean_inc(v_endExclusive_104_);
lean_inc(v_startInclusive_103_);
lean_inc_ref(v_str_102_);
v___x_111_ = l_String_Slice_pos_x21(v_s_101_, v___x_106_);
v_isSharedCheck_119_ = !lean_is_exclusive(v_s_101_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; lean_object* v_unused_121_; lean_object* v_unused_122_; 
v_unused_120_ = lean_ctor_get(v_s_101_, 2);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_s_101_, 1);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_s_101_, 0);
lean_dec(v_unused_122_);
v___x_113_ = v_s_101_;
v_isShared_114_ = v_isSharedCheck_119_;
goto v_resetjp_112_;
}
else
{
lean_dec(v_s_101_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_119_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_nat_add(v_startInclusive_103_, v___x_111_);
lean_dec(v___x_111_);
lean_dec(v_startInclusive_103_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_str_102_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_endExclusive_104_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object* v_s_123_, lean_object* v_pat_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_string_utf8_byte_size(v_s_123_);
v___x_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_127_, 0, v_s_123_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
v___x_128_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object* v_s_129_, lean_object* v_pat_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_s_129_, v_pat_130_);
lean_dec_ref(v_pat_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lean_load_plugin(lean_object* v_path_136_, lean_object* v_initFn_x3f_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_io_realpath(v_path_136_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_189_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_189_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_189_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_189_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_a_145_; 
if (lean_obj_tag(v_initFn_x3f_137_) == 0)
{
lean_object* v___x_172_; 
lean_inc(v_a_140_);
v___x_172_ = l_System_FilePath_fileStem(v_a_140_);
if (lean_obj_tag(v___x_172_) == 1)
{
lean_object* v_val_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_del_object(v___x_142_);
v_val_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_175_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_val_173_, v___x_174_);
v___x_176_ = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(v___x_175_);
v___x_177_ = ((lean_object*)(l_Lean_loadPlugin___closed__2));
v___x_178_ = l_String_Slice_toString(v___x_176_);
lean_dec_ref(v___x_176_);
v___x_179_ = lean_string_append(v___x_177_, v___x_178_);
lean_dec_ref(v___x_178_);
v_a_145_ = v___x_179_;
goto v___jp_144_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v___x_172_);
v___x_180_ = ((lean_object*)(l_Lean_loadPlugin___closed__3));
v___x_181_ = lean_string_append(v___x_180_, v_a_140_);
lean_dec(v_a_140_);
v___x_182_ = ((lean_object*)(l_Lean_loadPlugin___closed__1));
v___x_183_ = lean_string_append(v___x_181_, v___x_182_);
v___x_184_ = lean_mk_io_user_error(v___x_183_);
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 1);
lean_ctor_set(v___x_142_, 0, v___x_184_);
v___x_186_ = v___x_142_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_val_188_; 
lean_del_object(v___x_142_);
v_val_188_ = lean_ctor_get(v_initFn_x3f_137_, 0);
lean_inc(v_val_188_);
lean_dec_ref_known(v_initFn_x3f_137_, 1);
v_a_145_ = v_val_188_;
goto v___jp_144_;
}
v___jp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_dynlib_load(v_a_140_);
lean_dec(v_a_140_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_163_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_163_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_163_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_163_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_dynlib_get(v_a_147_, v_a_145_);
if (lean_obj_tag(v___x_151_) == 1)
{
lean_object* v_val_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_del_object(v___x_149_);
lean_dec_ref(v_a_145_);
v_val_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_151_, 1);
lean_inc(v_a_147_);
v___x_153_ = lean_runtime_mark_persistent(v_a_147_);
lean_dec(v___x_153_);
v___x_154_ = lean_dynlib_symbol_run_as_init(v_a_147_, v_val_152_);
lean_dec(v_val_152_);
lean_dec(v_a_147_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
lean_dec(v___x_151_);
lean_dec(v_a_147_);
v___x_155_ = ((lean_object*)(l_Lean_loadPlugin___closed__0));
v___x_156_ = lean_string_append(v___x_155_, v_a_145_);
lean_dec_ref(v_a_145_);
v___x_157_ = ((lean_object*)(l_Lean_loadPlugin___closed__1));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
v___x_159_ = lean_mk_io_user_error(v___x_158_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 1);
lean_ctor_set(v___x_149_, 0, v___x_159_);
v___x_161_ = v___x_149_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v_a_145_);
v_a_164_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_146_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_146_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_initFn_x3f_137_);
v_a_190_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_139_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_139_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object* v_path_198_, lean_object* v_initFn_x3f_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = lean_load_plugin(v_path_198_, v_initFn_x3f_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object* v_pat_202_, lean_object* v_s_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v_s_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object* v_pat_205_, lean_object* v_s_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(v_pat_205_, v_s_206_);
lean_dec_ref(v_pat_205_);
return v_res_207_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LoadDynlib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
