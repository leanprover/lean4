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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object*);
static const lean_string_object l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value;
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
lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4_;
v_res_4_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg();
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___redArg();
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(lean_object* v_dynlib_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(lean_object* v_dynlib_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(v_dynlib_9_);
lean_dec(v_dynlib_9_);
return v_res_10_;
}
}
LEAN_EXPORT void l_Lean_Dynlib_load_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_11_ = stack[0].m_obj;
lean_object* v_res_13_;
v_res_13_ = lean_dynlib_load(v_path_11_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_load___boxed(lean_object* v_path_14_, lean_object* v_a_00___x40___internal___hyg_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lean_dynlib_load(v_path_14_);
lean_dec_ref(v_path_14_);
return v_res_16_;
}
}
LEAN_EXPORT void l_Lean_Dynlib_get_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_dynlib_17_ = stack[0].m_obj;
lean_object* v_sym_18_ = stack[1].m_obj;
lean_object* v_res_19_;
v_res_19_ = lean_dynlib_get(v_dynlib_17_, v_sym_18_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_get_x3f___boxed(lean_object* v_dynlib_20_, lean_object* v_sym_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lean_dynlib_get(v_dynlib_20_, v_sym_21_);
lean_dec_ref(v_sym_21_);
lean_dec(v_dynlib_20_);
return v_res_22_;
}
}
LEAN_EXPORT void l_Lean_Dynlib_Symbol_runAsInit_0interp(lean_interpreter_value* stack)
{
lean_object* v_dynlib_23_ = stack[0].m_obj;
lean_object* v_sym_24_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = lean_dynlib_symbol_run_as_init(v_dynlib_23_, v_sym_24_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Dynlib_Symbol_runAsInit___boxed(lean_object* v_dynlib_27_, lean_object* v_sym_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lean_dynlib_symbol_run_as_init(v_dynlib_27_, v_sym_28_);
lean_dec(v_sym_28_);
lean_dec(v_dynlib_27_);
return v_res_30_;
}
}
lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(lean_object* v_dynlib_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_runtime_mark_persistent(v_dynlib_31_);
return v___x_33_;
}
}
LEAN_EXPORT void l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_dynlib_31_ = stack[0].m_obj;
lean_object* v_res_34_;
v_res_34_ = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(v_dynlib_31_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(lean_object* v_dynlib_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(v_dynlib_35_);
return v_res_37_;
}
}
lean_object* lean_load_dynlib(lean_object* v_path_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_dynlib_load(v_path_38_);
lean_dec_ref(v_path_38_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_50_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_50_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_50_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_50_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_45_ = lean_runtime_mark_persistent(v_a_41_);
lean_dec(v___x_45_);
v___x_46_ = lean_box(0);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_46_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_a_51_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_40_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_40_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT void lean_load_dynlib_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_38_ = stack[0].m_obj;
lean_object* v_res_59_;
v_res_59_ = lean_load_dynlib(v_path_38_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_loadDynlib___boxed(lean_object* v_path_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lean_load_dynlib(v_path_60_);
return v_res_62_;
}
}
lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(lean_object* v_dynlib_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_runtime_mark_persistent(v_dynlib_63_);
return v___x_65_;
}
}
LEAN_EXPORT void l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_dynlib_63_ = stack[0].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(v_dynlib_63_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(lean_object* v_dynlib_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(v_dynlib_67_);
return v_res_69_;
}
}
lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7(lean_object* v_dynlib_70_, lean_object* v_sym_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_dynlib_symbol_run_as_init(v_dynlib_70_, v_sym_71_);
return v___x_73_;
}
}
LEAN_EXPORT void l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_dynlib_70_ = stack[0].m_obj;
lean_object* v_sym_71_ = stack[1].m_obj;
lean_object* v_res_74_;
v_res_74_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7(v_dynlib_70_, v_sym_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7___boxed(lean_object* v_dynlib_75_, lean_object* v_sym_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__7(v_dynlib_75_, v_sym_76_);
lean_dec(v_sym_76_);
lean_dec(v_dynlib_75_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(lean_object* v_s_80_){
_start:
{
lean_object* v_str_81_; lean_object* v_startInclusive_82_; lean_object* v_endExclusive_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_str_81_ = lean_ctor_get(v_s_80_, 0);
v_startInclusive_82_ = lean_ctor_get(v_s_80_, 1);
v_endExclusive_83_ = lean_ctor_get(v_s_80_, 2);
v___x_84_ = lean_unsigned_to_nat(7u);
v___x_85_ = lean_nat_sub(v_endExclusive_83_, v_startInclusive_82_);
v___x_86_ = lean_nat_dec_le(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_dec(v___x_85_);
return v_s_80_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_87_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0));
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_nat_sub(v___x_85_, v___x_84_);
lean_dec(v___x_85_);
v___x_90_ = lean_nat_add(v_startInclusive_82_, v___x_89_);
v___x_91_ = lean_string_memcmp(v_str_81_, v___x_87_, v___x_90_, v___x_88_, v___x_84_);
lean_dec(v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v___x_89_);
return v_s_80_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
lean_inc(v_startInclusive_82_);
lean_inc_ref(v_str_81_);
v___x_92_ = l_String_Slice_pos_x21(v_s_80_, v___x_89_);
lean_dec(v___x_89_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_s_80_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_101_ = lean_ctor_get(v_s_80_, 2);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_s_80_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_s_80_, 0);
lean_dec(v_unused_103_);
v___x_94_ = v_s_80_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_dec(v_s_80_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_nat_add(v_startInclusive_82_, v___x_92_);
lean_dec(v___x_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 2, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_str_81_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_startInclusive_82_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v___x_96_);
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
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(lean_object* v_s_105_){
_start:
{
lean_object* v_str_106_; lean_object* v_startInclusive_107_; lean_object* v_endExclusive_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_str_106_ = lean_ctor_get(v_s_105_, 0);
v_startInclusive_107_ = lean_ctor_get(v_s_105_, 1);
v_endExclusive_108_ = lean_ctor_get(v_s_105_, 2);
v___x_109_ = lean_unsigned_to_nat(3u);
v___x_110_ = lean_nat_sub(v_endExclusive_108_, v_startInclusive_107_);
v___x_111_ = lean_nat_dec_le(v___x_109_, v___x_110_);
lean_dec(v___x_110_);
if (v___x_111_ == 0)
{
return v_s_105_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_string_memcmp(v_str_106_, v___x_112_, v_startInclusive_107_, v___x_113_, v___x_109_);
if (v___x_114_ == 0)
{
return v_s_105_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
lean_inc(v_endExclusive_108_);
lean_inc(v_startInclusive_107_);
lean_inc_ref(v_str_106_);
v___x_115_ = l_String_Slice_pos_x21(v_s_105_, v___x_109_);
v_isSharedCheck_123_ = !lean_is_exclusive(v_s_105_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; lean_object* v_unused_126_; 
v_unused_124_ = lean_ctor_get(v_s_105_, 2);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_s_105_, 1);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_s_105_, 0);
lean_dec(v_unused_126_);
v___x_117_ = v_s_105_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_dec(v_s_105_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_119_ = lean_nat_add(v_startInclusive_107_, v___x_115_);
lean_dec(v___x_115_);
lean_dec(v_startInclusive_107_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_str_106_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_endExclusive_108_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(lean_object* v_s_127_, lean_object* v_pat_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_string_utf8_byte_size(v_s_127_);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v_s_127_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
lean_ctor_set(v___x_131_, 2, v___x_130_);
v___x_132_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(lean_object* v_s_133_, lean_object* v_pat_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_s_133_, v_pat_134_);
lean_dec_ref(v_pat_134_);
return v_res_135_;
}
}
lean_object* lean_load_plugin(lean_object* v_path_140_, lean_object* v_initFn_x3f_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_io_realpath(v_path_140_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_193_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_193_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_193_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_193_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_a_149_; 
if (lean_obj_tag(v_initFn_x3f_141_) == 0)
{
lean_object* v___x_176_; 
lean_inc(v_a_144_);
v___x_176_ = l_System_FilePath_fileStem(v_a_144_);
if (lean_obj_tag(v___x_176_) == 1)
{
lean_object* v_val_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_del_object(v___x_146_);
v_val_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_176_, 1);
v___x_178_ = ((lean_object*)(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0));
v___x_179_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_val_177_, v___x_178_);
v___x_180_ = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(v___x_179_);
v___x_181_ = ((lean_object*)(l_Lean_loadPlugin___closed__2));
v___x_182_ = l_String_Slice_toString(v___x_180_);
lean_dec_ref(v___x_180_);
v___x_183_ = lean_string_append(v___x_181_, v___x_182_);
lean_dec_ref(v___x_182_);
v_a_149_ = v___x_183_;
goto v___jp_148_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec(v___x_176_);
v___x_184_ = ((lean_object*)(l_Lean_loadPlugin___closed__3));
v___x_185_ = lean_string_append(v___x_184_, v_a_144_);
lean_dec(v_a_144_);
v___x_186_ = ((lean_object*)(l_Lean_loadPlugin___closed__1));
v___x_187_ = lean_string_append(v___x_185_, v___x_186_);
v___x_188_ = lean_mk_io_user_error(v___x_187_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 1);
lean_ctor_set(v___x_146_, 0, v___x_188_);
v___x_190_ = v___x_146_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_object* v_val_192_; 
lean_del_object(v___x_146_);
v_val_192_ = lean_ctor_get(v_initFn_x3f_141_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_initFn_x3f_141_, 1);
v_a_149_ = v_val_192_;
goto v___jp_148_;
}
v___jp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_dynlib_load(v_a_144_);
lean_dec(v_a_144_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_167_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_167_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_167_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_167_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_dynlib_get(v_a_151_, v_a_149_);
if (lean_obj_tag(v___x_155_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_del_object(v___x_153_);
lean_dec_ref(v_a_149_);
v_val_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v___x_155_, 1);
lean_inc(v_a_151_);
v___x_157_ = lean_runtime_mark_persistent(v_a_151_);
lean_dec(v___x_157_);
v___x_158_ = lean_dynlib_symbol_run_as_init(v_a_151_, v_val_156_);
lean_dec(v_val_156_);
lean_dec(v_a_151_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_dec(v___x_155_);
lean_dec(v_a_151_);
v___x_159_ = ((lean_object*)(l_Lean_loadPlugin___closed__0));
v___x_160_ = lean_string_append(v___x_159_, v_a_149_);
lean_dec_ref(v_a_149_);
v___x_161_ = ((lean_object*)(l_Lean_loadPlugin___closed__1));
v___x_162_ = lean_string_append(v___x_160_, v___x_161_);
v___x_163_ = lean_mk_io_user_error(v___x_162_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 1);
lean_ctor_set(v___x_153_, 0, v___x_163_);
v___x_165_ = v___x_153_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v_a_149_);
v_a_168_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_150_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_150_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_initFn_x3f_141_);
v_a_194_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_143_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_143_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT void lean_load_plugin_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_140_ = stack[0].m_obj;
lean_object* v_initFn_x3f_141_ = stack[1].m_obj;
lean_object* v_res_202_;
v_res_202_ = lean_load_plugin(v_path_140_, v_initFn_x3f_141_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_loadPlugin___boxed(lean_object* v_path_203_, lean_object* v_initFn_x3f_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = lean_load_plugin(v_path_203_, v_initFn_x3f_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(lean_object* v_pat_207_, lean_object* v_s_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v_s_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(lean_object* v_pat_210_, lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(v_pat_210_, v_s_211_);
lean_dec_ref(v_pat_210_);
return v_res_212_;
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
