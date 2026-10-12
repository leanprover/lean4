// Lean compiler output
// Module: Init.Util
// Imports: public import Init.Data.ToString.Basic
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTrace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceVal(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace_if_shared(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTraceIfShared___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_stack_trace(lean_object*);
LEAN_EXPORT lean_object* l_dbgStackTrace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgStackTraceIf___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_dbgStackTraceIf___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgStackTraceIf(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_dbgStackTraceIf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_dbgSleep___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkPanicMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PANIC at "};
static const lean_object* l_mkPanicMessage___closed__0 = (const lean_object*)&l_mkPanicMessage___closed__0_value;
static const lean_string_object l_mkPanicMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_mkPanicMessage___closed__1 = (const lean_object*)&l_mkPanicMessage___closed__1_value;
static const lean_string_object l_mkPanicMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_mkPanicMessage___closed__2 = (const lean_object*)&l_mkPanicMessage___closed__2_value;
LEAN_EXPORT lean_object* l_mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkPanicMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkPanicMessageWithDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_mkPanicMessageWithDecl___closed__0 = (const lean_object*)&l_mkPanicMessageWithDecl___closed__0_value;
LEAN_EXPORT lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkPanicMessageWithDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPosWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_ptrAddrUnsafe___boxed(lean_object*, lean_object*);
uint8_t lean_is_exclusive_obj(lean_object*);
LEAN_EXPORT lean_object* l_isExclusiveUnsafe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ptrEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ptrEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEqList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ptrEqList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ptrEqList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEqUnsafe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEqUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEqDecEq___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEqDecEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEqDecEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT void l_dbgTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2_ = stack[1].m_obj;
lean_object* v_f_3_ = stack[2].m_obj;
lean_object* v_res_4_;
v_res_4_ = lean_dbg_trace(v_s_2_, v_f_3_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_dbgTrace___boxed(lean_object* v_00_u03b1_5_, lean_object* v_s_6_, lean_object* v_f_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lean_dbg_trace(v_s_6_, v_f_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg___lam__0(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
lean_inc(v_a_9_);
return v_a_9_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg___lam__0___boxed(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_dbgTraceVal___redArg___lam__0(v_a_11_, v_x_12_);
lean_dec(v_a_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg(lean_object* v_inst_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc(v_a_15_);
v___f_16_ = lean_alloc_closure((void*)(l_dbgTraceVal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v_a_15_);
v___x_17_ = lean_apply_1(v_inst_14_, v_a_15_);
v___x_18_ = lean_dbg_trace(v___x_17_, v___f_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_dbgTraceVal___redArg(v_inst_20_, v_a_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_dbgTraceIfShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_24_ = stack[1].m_obj;
lean_object* v_a_25_ = stack[2].m_obj;
lean_object* v_res_26_;
v_res_26_ = lean_dbg_trace_if_shared(v_s_24_, v_a_25_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_dbgTraceIfShared___boxed(lean_object* v_00_u03b1_27_, lean_object* v_s_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lean_dbg_trace_if_shared(v_s_28_, v_a_29_);
lean_dec_ref(v_s_28_);
return v_res_30_;
}
}
LEAN_EXPORT void l_dbgStackTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_32_ = stack[1].m_obj;
lean_object* v_res_33_;
v_res_33_ = lean_dbg_stack_trace(v_f_32_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_dbgStackTrace___boxed(lean_object* v_00_u03b1_34_, lean_object* v_f_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_dbg_stack_trace(v_f_35_);
return v_res_36_;
}
}
lean_object* l_dbgStackTraceIf___redArg(uint8_t v_cond_37_, lean_object* v_f_38_){
_start:
{
if (v_cond_37_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_f_38_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
v___x_41_ = lean_dbg_stack_trace(v_f_38_);
return v___x_41_;
}
}
}
LEAN_EXPORT void l_dbgStackTraceIf___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cond_37_ = stack[0].m_num;
lean_object* v_f_38_ = stack[1].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_dbgStackTraceIf___redArg(v_cond_37_, v_f_38_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_dbgStackTraceIf___redArg___boxed(lean_object* v_cond_43_, lean_object* v_f_44_){
_start:
{
uint8_t v_cond_boxed_45_; lean_object* v_res_46_; 
v_cond_boxed_45_ = lean_unbox(v_cond_43_);
v_res_46_ = l_dbgStackTraceIf___redArg(v_cond_boxed_45_, v_f_44_);
return v_res_46_;
}
}
lean_object* l_dbgStackTraceIf(lean_object* v_00_u03b1_47_, uint8_t v_cond_48_, lean_object* v_f_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_dbgStackTraceIf___redArg(v_cond_48_, v_f_49_);
return v___x_50_;
}
}
LEAN_EXPORT void l_dbgStackTraceIf_0interp(lean_interpreter_value* stack)
{
uint8_t v_cond_48_ = stack[1].m_num;
lean_object* v_f_49_ = stack[2].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_dbgStackTraceIf(lean_box(0), v_cond_48_, v_f_49_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_dbgStackTraceIf___boxed(lean_object* v_00_u03b1_52_, lean_object* v_cond_53_, lean_object* v_f_54_){
_start:
{
uint8_t v_cond_boxed_55_; lean_object* v_res_56_; 
v_cond_boxed_55_ = lean_unbox(v_cond_53_);
v_res_56_ = l_dbgStackTraceIf(v_00_u03b1_52_, v_cond_boxed_55_, v_f_54_);
return v_res_56_;
}
}
LEAN_EXPORT void l_dbgSleep_0interp(lean_interpreter_value* stack)
{
uint32_t v_ms_58_ = stack[1].m_num;
lean_object* v_f_59_ = stack[2].m_obj;
lean_object* v_res_60_;
v_res_60_ = lean_dbg_sleep(v_ms_58_, v_f_59_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_dbgSleep___boxed(lean_object* v_00_u03b1_61_, lean_object* v_ms_62_, lean_object* v_f_63_){
_start:
{
uint32_t v_ms_boxed_64_; lean_object* v_res_65_; 
v_ms_boxed_64_ = lean_unbox_uint32(v_ms_62_);
lean_dec(v_ms_62_);
v_res_65_ = lean_dbg_sleep(v_ms_boxed_64_, v_f_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessage(lean_object* v_modName_69_, lean_object* v_line_70_, lean_object* v_col_71_, lean_object* v_msg_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_73_ = ((lean_object*)(l_mkPanicMessage___closed__0));
v___x_74_ = lean_string_append(v___x_73_, v_modName_69_);
v___x_75_ = ((lean_object*)(l_mkPanicMessage___closed__1));
v___x_76_ = lean_string_append(v___x_74_, v___x_75_);
v___x_77_ = l_Nat_reprFast(v_line_70_);
v___x_78_ = lean_string_append(v___x_76_, v___x_77_);
lean_dec_ref(v___x_77_);
v___x_79_ = lean_string_append(v___x_78_, v___x_75_);
v___x_80_ = l_Nat_reprFast(v_col_71_);
v___x_81_ = lean_string_append(v___x_79_, v___x_80_);
lean_dec_ref(v___x_80_);
v___x_82_ = ((lean_object*)(l_mkPanicMessage___closed__2));
v___x_83_ = lean_string_append(v___x_81_, v___x_82_);
v___x_84_ = lean_string_append(v___x_83_, v_msg_72_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessage___boxed(lean_object* v_modName_85_, lean_object* v_line_86_, lean_object* v_col_87_, lean_object* v_msg_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_mkPanicMessage(v_modName_85_, v_line_86_, v_col_87_, v_msg_88_);
lean_dec_ref(v_msg_88_);
lean_dec_ref(v_modName_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___redArg(lean_object* v_inst_90_, lean_object* v_modName_91_, lean_object* v_line_92_, lean_object* v_col_93_, lean_object* v_msg_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = l_mkPanicMessage(v_modName_91_, v_line_92_, v_col_93_, v_msg_94_);
v___x_96_ = l_panic___redArg(v_inst_90_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___redArg___boxed(lean_object* v_inst_97_, lean_object* v_modName_98_, lean_object* v_line_99_, lean_object* v_col_100_, lean_object* v_msg_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_panicWithPos___redArg(v_inst_97_, v_modName_98_, v_line_99_, v_col_100_, v_msg_101_);
lean_dec_ref(v_msg_101_);
lean_dec_ref(v_modName_98_);
lean_dec(v_inst_97_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos(lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_modName_105_, lean_object* v_line_106_, lean_object* v_col_107_, lean_object* v_msg_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = l_mkPanicMessage(v_modName_105_, v_line_106_, v_col_107_, v_msg_108_);
v___x_110_ = l_panic___redArg(v_inst_104_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___boxed(lean_object* v_00_u03b1_111_, lean_object* v_inst_112_, lean_object* v_modName_113_, lean_object* v_line_114_, lean_object* v_col_115_, lean_object* v_msg_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_panicWithPos(v_00_u03b1_111_, v_inst_112_, v_modName_113_, v_line_114_, v_col_115_, v_msg_116_);
lean_dec_ref(v_msg_116_);
lean_dec_ref(v_modName_113_);
lean_dec(v_inst_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessageWithDecl(lean_object* v_modName_119_, lean_object* v_declName_120_, lean_object* v_line_121_, lean_object* v_col_122_, lean_object* v_msg_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_124_ = ((lean_object*)(l_mkPanicMessage___closed__0));
v___x_125_ = lean_string_append(v___x_124_, v_declName_120_);
v___x_126_ = ((lean_object*)(l_mkPanicMessageWithDecl___closed__0));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = lean_string_append(v___x_127_, v_modName_119_);
v___x_129_ = ((lean_object*)(l_mkPanicMessage___closed__1));
v___x_130_ = lean_string_append(v___x_128_, v___x_129_);
v___x_131_ = l_Nat_reprFast(v_line_121_);
v___x_132_ = lean_string_append(v___x_130_, v___x_131_);
lean_dec_ref(v___x_131_);
v___x_133_ = lean_string_append(v___x_132_, v___x_129_);
v___x_134_ = l_Nat_reprFast(v_col_122_);
v___x_135_ = lean_string_append(v___x_133_, v___x_134_);
lean_dec_ref(v___x_134_);
v___x_136_ = ((lean_object*)(l_mkPanicMessage___closed__2));
v___x_137_ = lean_string_append(v___x_135_, v___x_136_);
v___x_138_ = lean_string_append(v___x_137_, v_msg_123_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessageWithDecl___boxed(lean_object* v_modName_139_, lean_object* v_declName_140_, lean_object* v_line_141_, lean_object* v_col_142_, lean_object* v_msg_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_mkPanicMessageWithDecl(v_modName_139_, v_declName_140_, v_line_141_, v_col_142_, v_msg_143_);
lean_dec_ref(v_msg_143_);
lean_dec_ref(v_declName_140_);
lean_dec_ref(v_modName_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___redArg(lean_object* v_inst_145_, lean_object* v_modName_146_, lean_object* v_declName_147_, lean_object* v_line_148_, lean_object* v_col_149_, lean_object* v_msg_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = l_mkPanicMessageWithDecl(v_modName_146_, v_declName_147_, v_line_148_, v_col_149_, v_msg_150_);
v___x_152_ = l_panic___redArg(v_inst_145_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___redArg___boxed(lean_object* v_inst_153_, lean_object* v_modName_154_, lean_object* v_declName_155_, lean_object* v_line_156_, lean_object* v_col_157_, lean_object* v_msg_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_panicWithPosWithDecl___redArg(v_inst_153_, v_modName_154_, v_declName_155_, v_line_156_, v_col_157_, v_msg_158_);
lean_dec_ref(v_msg_158_);
lean_dec_ref(v_declName_155_);
lean_dec_ref(v_modName_154_);
lean_dec(v_inst_153_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl(lean_object* v_00_u03b1_160_, lean_object* v_inst_161_, lean_object* v_modName_162_, lean_object* v_declName_163_, lean_object* v_line_164_, lean_object* v_col_165_, lean_object* v_msg_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l_mkPanicMessageWithDecl(v_modName_162_, v_declName_163_, v_line_164_, v_col_165_, v_msg_166_);
v___x_168_ = l_panic___redArg(v_inst_161_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___boxed(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_modName_171_, lean_object* v_declName_172_, lean_object* v_line_173_, lean_object* v_col_174_, lean_object* v_msg_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_panicWithPosWithDecl(v_00_u03b1_169_, v_inst_170_, v_modName_171_, v_declName_172_, v_line_173_, v_col_174_, v_msg_175_);
lean_dec_ref(v_msg_175_);
lean_dec_ref(v_declName_172_);
lean_dec_ref(v_modName_171_);
lean_dec(v_inst_170_);
return v_res_176_;
}
}
LEAN_EXPORT void l_ptrAddrUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_178_ = stack[1].m_obj;
size_t v_res_179_;
v_res_179_ = lean_ptr_addr(v_a_178_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l_ptrAddrUnsafe___boxed(lean_object* v_00_u03b1_180_, lean_object* v_a_181_){
_start:
{
size_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = lean_ptr_addr(v_a_181_);
lean_dec(v_a_181_);
v_r_183_ = lean_box_usize(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT void l_isExclusiveUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_185_ = stack[1].m_obj;
uint8_t v_res_186_;
v_res_186_ = lean_is_exclusive_obj(v_a_185_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_isExclusiveUnsafe___boxed(lean_object* v_00_u03b1_187_, lean_object* v_a_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = lean_is_exclusive_obj(v_a_188_);
lean_dec(v_a_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___redArg(lean_object* v_a_191_, lean_object* v_k_192_){
_start:
{
size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_ptr_addr(v_a_191_);
v___x_194_ = lean_box_usize(v___x_193_);
v___x_195_ = lean_apply_1(v_k_192_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___redArg___boxed(lean_object* v_a_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_withPtrAddrUnsafe___redArg(v_a_196_, v_k_197_);
lean_dec(v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_a_201_, lean_object* v_k_202_, lean_object* v_h_203_){
_start:
{
size_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_ptr_addr(v_a_201_);
v___x_205_ = lean_box_usize(v___x_204_);
v___x_206_ = lean_apply_1(v_k_202_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___boxed(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_a_209_, lean_object* v_k_210_, lean_object* v_h_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_withPtrAddrUnsafe(v_00_u03b1_207_, v_00_u03b2_208_, v_a_209_, v_k_210_, v_h_211_);
lean_dec(v_a_209_);
return v_res_212_;
}
}
uint8_t l_ptrEq___redArg(lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
size_t v___x_215_; size_t v___x_216_; uint8_t v___x_217_; 
v___x_215_ = lean_ptr_addr(v_a_213_);
v___x_216_ = lean_ptr_addr(v_b_214_);
v___x_217_ = lean_usize_dec_eq(v___x_215_, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l_ptrEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_213_ = stack[0].m_obj;
lean_object* v_b_214_ = stack[1].m_obj;
uint8_t v_res_218_;
v_res_218_ = l_ptrEq___redArg(v_a_213_, v_b_214_);
stack->m_num = v_res_218_;
}
LEAN_EXPORT lean_object* l_ptrEq___redArg___boxed(lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_ptrEq___redArg(v_a_219_, v_b_220_);
lean_dec(v_b_220_);
lean_dec(v_a_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
uint8_t l_ptrEq(lean_object* v_00_u03b1_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
size_t v___x_226_; size_t v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_ptr_addr(v_a_224_);
v___x_227_ = lean_ptr_addr(v_b_225_);
v___x_228_ = lean_usize_dec_eq(v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT void l_ptrEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_224_ = stack[1].m_obj;
lean_object* v_b_225_ = stack[2].m_obj;
uint8_t v_res_229_;
v_res_229_ = l_ptrEq(lean_box(0), v_a_224_, v_b_225_);
stack->m_num = v_res_229_;
}
LEAN_EXPORT lean_object* l_ptrEq___boxed(lean_object* v_00_u03b1_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_ptrEq(v_00_u03b1_230_, v_a_231_, v_b_232_);
lean_dec(v_b_232_);
lean_dec(v_a_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
uint8_t l_ptrEqList___redArg(lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
if (lean_obj_tag(v_x_236_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = 1;
return v___x_237_;
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
}
else
{
if (lean_obj_tag(v_x_236_) == 1)
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v_head_241_; lean_object* v_tail_242_; size_t v___x_243_; size_t v___x_244_; uint8_t v___x_245_; 
v_head_239_ = lean_ctor_get(v_x_235_, 0);
v_tail_240_ = lean_ctor_get(v_x_235_, 1);
v_head_241_ = lean_ctor_get(v_x_236_, 0);
v_tail_242_ = lean_ctor_get(v_x_236_, 1);
v___x_243_ = lean_ptr_addr(v_head_239_);
v___x_244_ = lean_ptr_addr(v_head_241_);
v___x_245_ = lean_usize_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
return v___x_245_;
}
else
{
v_x_235_ = v_tail_240_;
v_x_236_ = v_tail_242_;
goto _start;
}
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
}
}
LEAN_EXPORT void l_ptrEqList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_235_ = stack[0].m_obj;
lean_object* v_x_236_ = stack[1].m_obj;
uint8_t v_res_248_;
v_res_248_ = l_ptrEqList___redArg(v_x_235_, v_x_236_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_ptrEqList___redArg___boxed(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_ptrEqList___redArg(v_x_249_, v_x_250_);
lean_dec(v_x_250_);
lean_dec(v_x_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
uint8_t l_ptrEqList(lean_object* v_00_u03b1_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = l_ptrEqList___redArg(v_x_254_, v_x_255_);
return v___x_256_;
}
}
LEAN_EXPORT void l_ptrEqList_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_254_ = stack[1].m_obj;
lean_object* v_x_255_ = stack[2].m_obj;
uint8_t v_res_257_;
v_res_257_ = l_ptrEqList(lean_box(0), v_x_254_, v_x_255_);
stack->m_num = v_res_257_;
}
LEAN_EXPORT lean_object* l_ptrEqList___boxed(lean_object* v_00_u03b1_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_ptrEqList(v_00_u03b1_258_, v_x_259_, v_x_260_);
lean_dec(v_x_260_);
lean_dec(v_x_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
uint8_t l_withPtrEqUnsafe___redArg(lean_object* v_a_263_, lean_object* v_b_264_, lean_object* v_k_265_){
_start:
{
size_t v___x_266_; size_t v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_ptr_addr(v_a_263_);
v___x_267_ = lean_ptr_addr(v_b_264_);
v___x_268_ = lean_usize_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_box(0);
v___x_270_ = lean_apply_1(v_k_265_, v___x_269_);
v___x_271_ = lean_unbox(v___x_270_);
return v___x_271_;
}
else
{
lean_dec_ref(v_k_265_);
return v___x_268_;
}
}
}
LEAN_EXPORT void l_withPtrEqUnsafe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_263_ = stack[0].m_obj;
lean_object* v_b_264_ = stack[1].m_obj;
lean_object* v_k_265_ = stack[2].m_obj;
uint8_t v_res_272_;
v_res_272_ = l_withPtrEqUnsafe___redArg(v_a_263_, v_b_264_, v_k_265_);
stack->m_num = v_res_272_;
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___redArg___boxed(lean_object* v_a_273_, lean_object* v_b_274_, lean_object* v_k_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_withPtrEqUnsafe___redArg(v_a_273_, v_b_274_, v_k_275_);
lean_dec(v_b_274_);
lean_dec(v_a_273_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
uint8_t l_withPtrEqUnsafe(lean_object* v_00_u03b1_278_, lean_object* v_a_279_, lean_object* v_b_280_, lean_object* v_k_281_, lean_object* v___h_282_){
_start:
{
size_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_ptr_addr(v_a_279_);
v___x_284_ = lean_ptr_addr(v_b_280_);
v___x_285_ = lean_usize_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_box(0);
v___x_287_ = lean_apply_1(v_k_281_, v___x_286_);
v___x_288_ = lean_unbox(v___x_287_);
return v___x_288_;
}
else
{
lean_dec_ref(v_k_281_);
return v___x_285_;
}
}
}
LEAN_EXPORT void l_withPtrEqUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_279_ = stack[1].m_obj;
lean_object* v_b_280_ = stack[2].m_obj;
lean_object* v_k_281_ = stack[3].m_obj;
uint8_t v_res_289_;
v_res_289_ = l_withPtrEqUnsafe(lean_box(0), v_a_279_, v_b_280_, v_k_281_, lean_box(0));
stack->m_num = v_res_289_;
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___boxed(lean_object* v_00_u03b1_290_, lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v_k_293_, lean_object* v___h_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_withPtrEqUnsafe(v_00_u03b1_290_, v_a_291_, v_b_292_, v_k_293_, v___h_294_);
lean_dec(v_b_292_);
lean_dec(v_a_291_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
uint8_t l_withPtrEq___redArg(lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v_k_299_){
_start:
{
size_t v___x_300_; size_t v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_ptr_addr(v_a_297_);
v___x_301_ = lean_ptr_addr(v_b_298_);
v___x_302_ = lean_usize_dec_eq(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_1(v_k_299_, v___x_303_);
v___x_305_ = lean_unbox(v___x_304_);
return v___x_305_;
}
else
{
lean_dec_ref(v_k_299_);
return v___x_302_;
}
}
}
LEAN_EXPORT void l_withPtrEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_297_ = stack[0].m_obj;
lean_object* v_b_298_ = stack[1].m_obj;
lean_object* v_k_299_ = stack[2].m_obj;
uint8_t v_res_306_;
v_res_306_ = l_withPtrEq___redArg(v_a_297_, v_b_298_, v_k_299_);
stack->m_num = v_res_306_;
}
LEAN_EXPORT lean_object* l_withPtrEq___redArg___boxed(lean_object* v_a_307_, lean_object* v_b_308_, lean_object* v_k_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_withPtrEq___redArg(v_a_307_, v_b_308_, v_k_309_);
lean_dec(v_b_308_);
lean_dec(v_a_307_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
uint8_t l_withPtrEq(lean_object* v_00_u03b1_312_, lean_object* v_a_313_, lean_object* v_b_314_, lean_object* v_k_315_, lean_object* v_h_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_withPtrEq___redArg(v_a_313_, v_b_314_, v_k_315_);
return v___x_317_;
}
}
LEAN_EXPORT void l_withPtrEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_313_ = stack[1].m_obj;
lean_object* v_b_314_ = stack[2].m_obj;
lean_object* v_k_315_ = stack[3].m_obj;
uint8_t v_res_318_;
v_res_318_ = l_withPtrEq(lean_box(0), v_a_313_, v_b_314_, v_k_315_, lean_box(0));
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_withPtrEq___boxed(lean_object* v_00_u03b1_319_, lean_object* v_a_320_, lean_object* v_b_321_, lean_object* v_k_322_, lean_object* v_h_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_withPtrEq(v_00_u03b1_319_, v_a_320_, v_b_321_, v_k_322_, v_h_323_);
lean_dec(v_b_321_);
lean_dec(v_a_320_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
uint8_t l_withPtrEqDecEq___redArg___lam__0(lean_object* v_k_326_, lean_object* v_x_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_box(0);
v___x_329_ = lean_apply_1(v_k_326_, v___x_328_);
v___x_330_ = lean_unbox(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT void l_withPtrEqDecEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_326_ = stack[0].m_obj;
lean_object* v_x_327_ = stack[1].m_obj;
uint8_t v_res_331_;
v_res_331_ = l_withPtrEqDecEq___redArg___lam__0(v_k_326_, v_x_327_);
stack->m_num = v_res_331_;
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___redArg___lam__0___boxed(lean_object* v_k_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_withPtrEqDecEq___redArg___lam__0(v_k_332_, v_x_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
uint8_t l_withPtrEqDecEq___redArg(lean_object* v_withPtrEq_336_, lean_object* v_a_337_, lean_object* v_b_338_, lean_object* v_k_339_){
_start:
{
lean_object* v___f_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___f_340_ = lean_alloc_closure((void*)(l_withPtrEqDecEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_340_, 0, v_k_339_);
v___x_341_ = lean_apply_4(v_withPtrEq_336_, v_a_337_, v_b_338_, v___f_340_, lean_box(0));
v___x_342_ = lean_unbox(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT void l_withPtrEqDecEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_withPtrEq_336_ = stack[0].m_obj;
lean_object* v_a_337_ = stack[1].m_obj;
lean_object* v_b_338_ = stack[2].m_obj;
lean_object* v_k_339_ = stack[3].m_obj;
uint8_t v_res_343_;
v_res_343_ = l_withPtrEqDecEq___redArg(v_withPtrEq_336_, v_a_337_, v_b_338_, v_k_339_);
stack->m_num = v_res_343_;
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___redArg___boxed(lean_object* v_withPtrEq_344_, lean_object* v_a_345_, lean_object* v_b_346_, lean_object* v_k_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_withPtrEqDecEq___redArg(v_withPtrEq_344_, v_a_345_, v_b_346_, v_k_347_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
uint8_t l_withPtrEqDecEq(lean_object* v_00_u03b1_350_, lean_object* v_withPtrEq_351_, lean_object* v_hw_352_, lean_object* v_a_353_, lean_object* v_b_354_, lean_object* v_k_355_){
_start:
{
lean_object* v___f_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___f_356_ = lean_alloc_closure((void*)(l_withPtrEqDecEq___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_356_, 0, v_k_355_);
v___x_357_ = lean_apply_4(v_withPtrEq_351_, v_a_353_, v_b_354_, v___f_356_, lean_box(0));
v___x_358_ = lean_unbox(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT void l_withPtrEqDecEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_withPtrEq_351_ = stack[1].m_obj;
lean_object* v_a_353_ = stack[3].m_obj;
lean_object* v_b_354_ = stack[4].m_obj;
lean_object* v_k_355_ = stack[5].m_obj;
uint8_t v_res_359_;
v_res_359_ = l_withPtrEqDecEq(lean_box(0), v_withPtrEq_351_, lean_box(0), v_a_353_, v_b_354_, v_k_355_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___boxed(lean_object* v_00_u03b1_360_, lean_object* v_withPtrEq_361_, lean_object* v_hw_362_, lean_object* v_a_363_, lean_object* v_b_364_, lean_object* v_k_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_withPtrEqDecEq(v_00_u03b1_360_, v_withPtrEq_361_, v_hw_362_, v_a_363_, v_b_364_, v_k_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Util(builtin);
}
#ifdef __cplusplus
}
#endif
