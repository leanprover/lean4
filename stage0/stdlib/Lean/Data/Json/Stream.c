// Lean compiler output
// Module: Lean.Data.Json.Stream
// Imports: public import Lean.Data.Json.Parser public import Lean.Data.Json.Printer
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
lean_object* l_Lean_Json_compress(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
static const lean_string_object l_IO_FS_Stream_readUTF8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid UTF-8"};
static const lean_object* l_IO_FS_Stream_readUTF8___closed__0 = (const lean_object*)&l_IO_FS_Stream_readUTF8___closed__0_value;
static lean_once_cell_t l_IO_FS_Stream_readUTF8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_readUTF8___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_IO_FS_Stream_readUTF8___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_IO_FS_Stream_readUTF8___closed__0));
v___x_3_ = lean_mk_io_user_error(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8(lean_object* v_h_4_, lean_object* v_nBytes_5_){
_start:
{
lean_object* v_read_7_; size_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_read_7_ = lean_ctor_get(v_h_4_, 1);
lean_inc_ref(v_read_7_);
lean_dec_ref(v_h_4_);
v___x_8_ = lean_usize_of_nat(v_nBytes_5_);
v___x_9_ = lean_box_usize(v___x_8_);
v___x_10_ = lean_apply_2(v_read_7_, v___x_9_, lean_box(0));
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_24_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_24_ == 0)
{
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_24_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_24_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
uint8_t v___x_15_; 
v___x_15_ = lean_string_validate_utf8(v_a_11_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_18_; 
lean_dec(v_a_11_);
v___x_16_ = lean_obj_once(&l_IO_FS_Stream_readUTF8___closed__1, &l_IO_FS_Stream_readUTF8___closed__1_once, _init_l_IO_FS_Stream_readUTF8___closed__1);
if (v_isShared_14_ == 0)
{
lean_ctor_set_tag(v___x_13_, 1);
lean_ctor_set(v___x_13_, 0, v___x_16_);
v___x_18_ = v___x_13_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v___x_16_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
else
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = lean_string_from_utf8_unchecked(v_a_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_20_);
v___x_22_ = v___x_13_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
v_a_25_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_10_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_10_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readUTF8___boxed(lean_object* v_h_33_, lean_object* v_nBytes_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_IO_FS_Stream_readUTF8(v_h_33_, v_nBytes_34_);
lean_dec(v_nBytes_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(lean_object* v_e_37_){
_start:
{
if (lean_obj_tag(v_e_37_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
v_a_39_ = lean_ctor_get(v_e_37_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_e_37_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v_e_37_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v_e_37_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = lean_mk_io_user_error(v_a_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set_tag(v___x_41_, 1);
lean_ctor_set(v___x_41_, 0, v___x_43_);
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v_a_48_ = lean_ctor_get(v_e_37_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_e_37_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v_e_37_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v_e_37_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set_tag(v___x_50_, 0);
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg___boxed(lean_object* v_e_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(v_e_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(lean_object* v_00_u03b1_59_, lean_object* v_e_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(v_e_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___boxed(lean_object* v_00_u03b1_63_, lean_object* v_e_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(v_00_u03b1_63_, v_e_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson(lean_object* v_h_67_, lean_object* v_nBytes_68_){
_start:
{
lean_object* v_read_70_; size_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_read_70_ = lean_ctor_get(v_h_67_, 1);
lean_inc_ref(v_read_70_);
lean_dec_ref(v_h_67_);
v___x_71_ = lean_usize_of_nat(v_nBytes_68_);
v___x_72_ = lean_box_usize(v___x_71_);
v___x_73_ = lean_apply_2(v_read_70_, v___x_72_, lean_box(0));
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_86_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_86_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_86_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_86_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint8_t v___x_78_; 
v___x_78_ = lean_string_validate_utf8(v_a_74_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_81_; 
lean_dec(v_a_74_);
v___x_79_ = lean_obj_once(&l_IO_FS_Stream_readUTF8___closed__1, &l_IO_FS_Stream_readUTF8___closed__1_once, _init_l_IO_FS_Stream_readUTF8___closed__1);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 1);
lean_ctor_set(v___x_76_, 0, v___x_79_);
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_del_object(v___x_76_);
v___x_83_ = lean_string_from_utf8_unchecked(v_a_74_);
v___x_84_ = l_Lean_Json_parse(v___x_83_);
v___x_85_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(v___x_84_);
return v___x_85_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_a_87_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_73_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_73_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readJson___boxed(lean_object* v_h_95_, lean_object* v_nBytes_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_IO_FS_Stream_readJson(v_h_95_, v_nBytes_96_);
lean_dec(v_nBytes_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson(lean_object* v_h_99_, lean_object* v_j_100_){
_start:
{
lean_object* v_flush_102_; lean_object* v_putStr_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_flush_102_ = lean_ctor_get(v_h_99_, 0);
lean_inc_ref(v_flush_102_);
v_putStr_103_ = lean_ctor_get(v_h_99_, 4);
lean_inc_ref(v_putStr_103_);
lean_dec_ref(v_h_99_);
v___x_104_ = l_Lean_Json_compress(v_j_100_);
v___x_105_ = lean_apply_2(v_putStr_103_, v___x_104_, lean_box(0));
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v___x_106_; 
lean_dec_ref(v___x_105_);
v___x_106_ = lean_apply_1(v_flush_102_, lean_box(0));
return v___x_106_;
}
else
{
lean_dec_ref(v_flush_102_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeJson___boxed(lean_object* v_h_107_, lean_object* v_j_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_IO_FS_Stream_writeJson(v_h_107_, v_j_108_);
return v_res_110_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_Stream(builtin);
}
#ifdef __cplusplus
}
#endif
