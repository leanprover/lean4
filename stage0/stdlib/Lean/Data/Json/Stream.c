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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readUTF8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid UTF-8"};
static const lean_object* l_Lean_IO_FS_Stream_readUTF8___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readUTF8___closed__0_value;
static lean_once_cell_t l_Lean_IO_FS_Stream_readUTF8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_readUTF8___closed__1;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readUTF8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readJson___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeJson___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IO_FS_Stream_readUTF8___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_IO_FS_Stream_readUTF8___closed__0));
v___x_3_ = lean_mk_io_user_error(v___x_2_);
return v___x_3_;
}
}
lean_object* l_Lean_IO_FS_Stream_readUTF8(lean_object* v_h_4_, lean_object* v_nBytes_5_){
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
v___x_16_ = lean_obj_once(&l_Lean_IO_FS_Stream_readUTF8___closed__1, &l_Lean_IO_FS_Stream_readUTF8___closed__1_once, _init_l_Lean_IO_FS_Stream_readUTF8___closed__1);
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
LEAN_EXPORT void l_Lean_IO_FS_Stream_readUTF8_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_4_ = stack[0].m_obj;
lean_object* v_nBytes_5_ = stack[1].m_obj;
lean_object* v_res_33_;
v_res_33_ = l_Lean_IO_FS_Stream_readUTF8(v_h_4_, v_nBytes_5_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readUTF8___boxed(lean_object* v_h_34_, lean_object* v_nBytes_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_IO_FS_Stream_readUTF8(v_h_34_, v_nBytes_35_);
lean_dec(v_nBytes_35_);
return v_res_37_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg(lean_object* v_e_38_){
_start:
{
if (lean_obj_tag(v_e_38_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_48_; 
v_a_40_ = lean_ctor_get(v_e_38_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v_e_38_);
if (v_isSharedCheck_48_ == 0)
{
v___x_42_ = v_e_38_;
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v_e_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_mk_io_user_error(v_a_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set_tag(v___x_42_, 1);
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v_e_38_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v_e_38_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v_e_38_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v_e_38_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 0);
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_38_ = stack[0].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg(v_e_38_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg___boxed(lean_object* v_e_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg(v_e_58_);
return v_res_60_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0(lean_object* v_00_u03b1_61_, lean_object* v_e_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg(v_e_62_);
return v___x_64_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_62_ = stack[1].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0(lean_box(0), v_e_62_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___boxed(lean_object* v_00_u03b1_66_, lean_object* v_e_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0(v_00_u03b1_66_, v_e_67_);
return v_res_69_;
}
}
lean_object* l_Lean_IO_FS_Stream_readJson(lean_object* v_h_70_, lean_object* v_nBytes_71_){
_start:
{
lean_object* v_read_73_; size_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_read_73_ = lean_ctor_get(v_h_70_, 1);
lean_inc_ref(v_read_73_);
lean_dec_ref(v_h_70_);
v___x_74_ = lean_usize_of_nat(v_nBytes_71_);
v___x_75_ = lean_box_usize(v___x_74_);
v___x_76_ = lean_apply_2(v_read_73_, v___x_75_, lean_box(0));
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_89_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_89_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = lean_string_validate_utf8(v_a_77_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_a_77_);
v___x_82_ = lean_obj_once(&l_Lean_IO_FS_Stream_readUTF8___closed__1, &l_Lean_IO_FS_Stream_readUTF8___closed__1_once, _init_l_Lean_IO_FS_Stream_readUTF8___closed__1);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 1);
lean_ctor_set(v___x_79_, 0, v___x_82_);
v___x_84_ = v___x_79_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_del_object(v___x_79_);
v___x_86_ = lean_string_from_utf8_unchecked(v_a_77_);
v___x_87_ = l_Lean_Json_parse(v___x_86_);
v___x_88_ = l_IO_ofExcept___at___00Lean_IO_FS_Stream_readJson_spec__0___redArg(v___x_87_);
return v___x_88_;
}
}
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_a_90_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_76_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_76_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readJson_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_70_ = stack[0].m_obj;
lean_object* v_nBytes_71_ = stack[1].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_IO_FS_Stream_readJson(v_h_70_, v_nBytes_71_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readJson___boxed(lean_object* v_h_99_, lean_object* v_nBytes_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_IO_FS_Stream_readJson(v_h_99_, v_nBytes_100_);
lean_dec(v_nBytes_100_);
return v_res_102_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeJson(lean_object* v_h_103_, lean_object* v_j_104_){
_start:
{
lean_object* v_flush_106_; lean_object* v_putStr_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_flush_106_ = lean_ctor_get(v_h_103_, 0);
lean_inc_ref(v_flush_106_);
v_putStr_107_ = lean_ctor_get(v_h_103_, 4);
lean_inc_ref(v_putStr_107_);
lean_dec_ref(v_h_103_);
v___x_108_ = l_Lean_Json_compress(v_j_104_);
v___x_109_ = lean_apply_2(v_putStr_107_, v___x_108_, lean_box(0));
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_110_; 
lean_dec_ref_known(v___x_109_, 1);
v___x_110_ = lean_apply_1(v_flush_106_, lean_box(0));
return v___x_110_;
}
else
{
lean_dec_ref(v_flush_106_);
return v___x_109_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeJson_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_103_ = stack[0].m_obj;
lean_object* v_j_104_ = stack[1].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_IO_FS_Stream_writeJson(v_h_103_, v_j_104_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeJson___boxed(lean_object* v_h_112_, lean_object* v_j_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_IO_FS_Stream_writeJson(v_h_112_, v_j_113_);
return v_res_115_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
