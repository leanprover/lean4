// Lean compiler output
// Module: Init.Data.ByteArray.Extra
// Imports: public import Init.Data.ByteArray.Basic import Init.Data.String.Defs import Init.Data.UInt.Basic
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
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static const lean_ctor_object l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1 = (const lean_object*)&l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1_value;
LEAN_EXPORT uint64_t l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_ByteArray_toUInt64LE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.ByteArray.Extra"};
static const lean_object* l_ByteArray_toUInt64LE_x21___closed__0 = (const lean_object*)&l_ByteArray_toUInt64LE_x21___closed__0_value;
static const lean_string_object l_ByteArray_toUInt64LE_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ByteArray.toUInt64LE!"};
static const lean_object* l_ByteArray_toUInt64LE_x21___closed__1 = (const lean_object*)&l_ByteArray_toUInt64LE_x21___closed__1_value;
static const lean_string_object l_ByteArray_toUInt64LE_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "assertion violation: bs.size == 8\n  "};
static const lean_object* l_ByteArray_toUInt64LE_x21___closed__2 = (const lean_object*)&l_ByteArray_toUInt64LE_x21___closed__2_value;
static lean_once_cell_t l_ByteArray_toUInt64LE_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_toUInt64LE_x21___closed__3;
LEAN_EXPORT uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21___boxed(lean_object*);
static const lean_string_object l_ByteArray_toUInt64BE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ByteArray.toUInt64BE!"};
static const lean_object* l_ByteArray_toUInt64BE_x21___closed__0 = (const lean_object*)&l_ByteArray_toUInt64BE_x21___closed__0_value;
static lean_once_cell_t l_ByteArray_toUInt64BE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ByteArray_toUInt64BE_x21___closed__1;
LEAN_EXPORT uint64_t l_ByteArray_toUInt64BE_x21(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object*);
uint64_t l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(lean_object* v_msg_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint64_t v___x_6_; 
v___x_4_ = ((lean_object*)(l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1));
v___x_5_ = lean_panic_fn_borrowed(v___x_4_, v_msg_3_);
v___x_6_ = lean_unbox_uint64(v___x_5_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_panic___at___00ByteArray_toUInt64LE_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3_ = stack[0].m_obj;
uint64_t v_res_7_;
v_res_7_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v_msg_3_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed(lean_object* v_msg_8_){
_start:
{
uint64_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v_msg_8_);
v_r_10_ = lean_box_uint64(v_res_9_);
return v_r_10_;
}
}
static lean_object* _init_l_ByteArray_toUInt64LE_x21___closed__3(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_14_ = ((lean_object*)(l_ByteArray_toUInt64LE_x21___closed__2));
v___x_15_ = lean_unsigned_to_nat(2u);
v___x_16_ = lean_unsigned_to_nat(21u);
v___x_17_ = ((lean_object*)(l_ByteArray_toUInt64LE_x21___closed__1));
v___x_18_ = ((lean_object*)(l_ByteArray_toUInt64LE_x21___closed__0));
v___x_19_ = l_mkPanicMessageWithDecl(v___x_18_, v___x_17_, v___x_16_, v___x_15_, v___x_14_);
return v___x_19_;
}
}
uint64_t l_ByteArray_toUInt64LE_x21(lean_object* v_bs_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = lean_byte_array_size(v_bs_20_);
v___x_22_ = lean_unsigned_to_nat(8u);
v___x_23_ = lean_nat_dec_eq(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; uint64_t v___x_25_; 
v___x_24_ = lean_obj_once(&l_ByteArray_toUInt64LE_x21___closed__3, &l_ByteArray_toUInt64LE_x21___closed__3_once, _init_l_ByteArray_toUInt64LE_x21___closed__3);
v___x_25_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v___x_35_; uint64_t v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; 
v___x_26_ = lean_unsigned_to_nat(7u);
v___x_27_ = lean_byte_array_get(v_bs_20_, v___x_26_);
v___x_28_ = lean_uint8_to_uint64(v___x_27_);
v___x_29_ = 56ULL;
v___x_30_ = lean_uint64_shift_left(v___x_28_, v___x_29_);
v___x_31_ = lean_unsigned_to_nat(6u);
v___x_32_ = lean_byte_array_get(v_bs_20_, v___x_31_);
v___x_33_ = lean_uint8_to_uint64(v___x_32_);
v___x_34_ = 48ULL;
v___x_35_ = lean_uint64_shift_left(v___x_33_, v___x_34_);
v___x_36_ = lean_uint64_lor(v___x_30_, v___x_35_);
v___x_37_ = lean_unsigned_to_nat(5u);
v___x_38_ = lean_byte_array_get(v_bs_20_, v___x_37_);
v___x_39_ = lean_uint8_to_uint64(v___x_38_);
v___x_40_ = 40ULL;
v___x_41_ = lean_uint64_shift_left(v___x_39_, v___x_40_);
v___x_42_ = lean_uint64_lor(v___x_36_, v___x_41_);
v___x_43_ = lean_unsigned_to_nat(4u);
v___x_44_ = lean_byte_array_get(v_bs_20_, v___x_43_);
v___x_45_ = lean_uint8_to_uint64(v___x_44_);
v___x_46_ = 32ULL;
v___x_47_ = lean_uint64_shift_left(v___x_45_, v___x_46_);
v___x_48_ = lean_uint64_lor(v___x_42_, v___x_47_);
v___x_49_ = lean_unsigned_to_nat(3u);
v___x_50_ = lean_byte_array_get(v_bs_20_, v___x_49_);
v___x_51_ = lean_uint8_to_uint64(v___x_50_);
v___x_52_ = 24ULL;
v___x_53_ = lean_uint64_shift_left(v___x_51_, v___x_52_);
v___x_54_ = lean_uint64_lor(v___x_48_, v___x_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v___x_56_ = lean_byte_array_get(v_bs_20_, v___x_55_);
v___x_57_ = lean_uint8_to_uint64(v___x_56_);
v___x_58_ = 16ULL;
v___x_59_ = lean_uint64_shift_left(v___x_57_, v___x_58_);
v___x_60_ = lean_uint64_lor(v___x_54_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_byte_array_get(v_bs_20_, v___x_61_);
v___x_63_ = lean_uint8_to_uint64(v___x_62_);
v___x_64_ = 8ULL;
v___x_65_ = lean_uint64_shift_left(v___x_63_, v___x_64_);
v___x_66_ = lean_uint64_lor(v___x_60_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_byte_array_get(v_bs_20_, v___x_67_);
v___x_69_ = lean_uint8_to_uint64(v___x_68_);
v___x_70_ = lean_uint64_lor(v___x_66_, v___x_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT void l_ByteArray_toUInt64LE_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_20_ = stack[0].m_obj;
uint64_t v_res_71_;
v_res_71_ = l_ByteArray_toUInt64LE_x21(v_bs_20_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64LE_x21___boxed(lean_object* v_bs_72_){
_start:
{
uint64_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_ByteArray_toUInt64LE_x21(v_bs_72_);
lean_dec_ref(v_bs_72_);
v_r_74_ = lean_box_uint64(v_res_73_);
return v_r_74_;
}
}
static lean_object* _init_l_ByteArray_toUInt64BE_x21___closed__1(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_76_ = ((lean_object*)(l_ByteArray_toUInt64LE_x21___closed__2));
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_unsigned_to_nat(37u);
v___x_79_ = ((lean_object*)(l_ByteArray_toUInt64BE_x21___closed__0));
v___x_80_ = ((lean_object*)(l_ByteArray_toUInt64LE_x21___closed__0));
v___x_81_ = l_mkPanicMessageWithDecl(v___x_80_, v___x_79_, v___x_78_, v___x_77_, v___x_76_);
return v___x_81_;
}
}
uint64_t l_ByteArray_toUInt64BE_x21(lean_object* v_bs_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_byte_array_size(v_bs_82_);
v___x_84_ = lean_unsigned_to_nat(8u);
v___x_85_ = lean_nat_dec_eq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint64_t v___x_87_; 
v___x_86_ = lean_obj_once(&l_ByteArray_toUInt64BE_x21___closed__1, &l_ByteArray_toUInt64BE_x21___closed__1_once, _init_l_ByteArray_toUInt64BE_x21___closed__1);
v___x_87_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v___x_86_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_byte_array_get(v_bs_82_, v___x_88_);
v___x_90_ = lean_uint8_to_uint64(v___x_89_);
v___x_91_ = 56ULL;
v___x_92_ = lean_uint64_shift_left(v___x_90_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_byte_array_get(v_bs_82_, v___x_93_);
v___x_95_ = lean_uint8_to_uint64(v___x_94_);
v___x_96_ = 48ULL;
v___x_97_ = lean_uint64_shift_left(v___x_95_, v___x_96_);
v___x_98_ = lean_uint64_lor(v___x_92_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(2u);
v___x_100_ = lean_byte_array_get(v_bs_82_, v___x_99_);
v___x_101_ = lean_uint8_to_uint64(v___x_100_);
v___x_102_ = 40ULL;
v___x_103_ = lean_uint64_shift_left(v___x_101_, v___x_102_);
v___x_104_ = lean_uint64_lor(v___x_98_, v___x_103_);
v___x_105_ = lean_unsigned_to_nat(3u);
v___x_106_ = lean_byte_array_get(v_bs_82_, v___x_105_);
v___x_107_ = lean_uint8_to_uint64(v___x_106_);
v___x_108_ = 32ULL;
v___x_109_ = lean_uint64_shift_left(v___x_107_, v___x_108_);
v___x_110_ = lean_uint64_lor(v___x_104_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(4u);
v___x_112_ = lean_byte_array_get(v_bs_82_, v___x_111_);
v___x_113_ = lean_uint8_to_uint64(v___x_112_);
v___x_114_ = 24ULL;
v___x_115_ = lean_uint64_shift_left(v___x_113_, v___x_114_);
v___x_116_ = lean_uint64_lor(v___x_110_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(5u);
v___x_118_ = lean_byte_array_get(v_bs_82_, v___x_117_);
v___x_119_ = lean_uint8_to_uint64(v___x_118_);
v___x_120_ = 16ULL;
v___x_121_ = lean_uint64_shift_left(v___x_119_, v___x_120_);
v___x_122_ = lean_uint64_lor(v___x_116_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(6u);
v___x_124_ = lean_byte_array_get(v_bs_82_, v___x_123_);
v___x_125_ = lean_uint8_to_uint64(v___x_124_);
v___x_126_ = 8ULL;
v___x_127_ = lean_uint64_shift_left(v___x_125_, v___x_126_);
v___x_128_ = lean_uint64_lor(v___x_122_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(7u);
v___x_130_ = lean_byte_array_get(v_bs_82_, v___x_129_);
v___x_131_ = lean_uint8_to_uint64(v___x_130_);
v___x_132_ = lean_uint64_lor(v___x_128_, v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT void l_ByteArray_toUInt64BE_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_82_ = stack[0].m_obj;
uint64_t v_res_133_;
v_res_133_ = l_ByteArray_toUInt64BE_x21(v_bs_82_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_ByteArray_toUInt64BE_x21___boxed(lean_object* v_bs_134_){
_start:
{
uint64_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_ByteArray_toUInt64BE_x21(v_bs_134_);
lean_dec_ref(v_bs_134_);
v_r_136_ = lean_box_uint64(v_res_135_);
return v_r_136_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ByteArray_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ByteArray_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
