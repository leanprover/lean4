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
LEAN_EXPORT uint8_t l_withPtrEqDecEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_withPtrEqDecEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withPtrEqDecEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dbgTrace___boxed(lean_object* v_00_u03b1_4_, lean_object* v_s_5_, lean_object* v_f_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lean_dbg_trace(v_s_5_, v_f_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg___lam__0(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
lean_inc(v_a_8_);
return v_a_8_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg___lam__0___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_dbgTraceVal___redArg___lam__0(v_a_10_, v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal___redArg(lean_object* v_inst_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_inc(v_a_14_);
v___f_15_ = lean_alloc_closure((void*)(l_dbgTraceVal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_15_, 0, v_a_14_);
v___x_16_ = lean_apply_1(v_inst_13_, v_a_14_);
v___x_17_ = lean_dbg_trace(v___x_16_, v___f_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceVal(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_dbgTraceVal___redArg(v_inst_19_, v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_dbgTraceIfShared___boxed(lean_object* v_00_u03b1_25_, lean_object* v_s_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lean_dbg_trace_if_shared(v_s_26_, v_a_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_dbgStackTrace___boxed(lean_object* v_00_u03b1_31_, lean_object* v_f_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lean_dbg_stack_trace(v_f_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_dbgStackTraceIf___redArg(uint8_t v_cond_34_, lean_object* v_f_35_){
_start:
{
if (v_cond_34_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_f_35_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_dbg_stack_trace(v_f_35_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_dbgStackTraceIf___redArg___boxed(lean_object* v_cond_39_, lean_object* v_f_40_){
_start:
{
uint8_t v_cond_boxed_41_; lean_object* v_res_42_; 
v_cond_boxed_41_ = lean_unbox(v_cond_39_);
v_res_42_ = l_dbgStackTraceIf___redArg(v_cond_boxed_41_, v_f_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_dbgStackTraceIf(lean_object* v_00_u03b1_43_, uint8_t v_cond_44_, lean_object* v_f_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_dbgStackTraceIf___redArg(v_cond_44_, v_f_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_dbgStackTraceIf___boxed(lean_object* v_00_u03b1_47_, lean_object* v_cond_48_, lean_object* v_f_49_){
_start:
{
uint8_t v_cond_boxed_50_; lean_object* v_res_51_; 
v_cond_boxed_50_ = lean_unbox(v_cond_48_);
v_res_51_ = l_dbgStackTraceIf(v_00_u03b1_47_, v_cond_boxed_50_, v_f_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_dbgSleep___boxed(lean_object* v_00_u03b1_55_, lean_object* v_ms_56_, lean_object* v_f_57_){
_start:
{
uint32_t v_ms_boxed_58_; lean_object* v_res_59_; 
v_ms_boxed_58_ = lean_unbox_uint32(v_ms_56_);
lean_dec(v_ms_56_);
v_res_59_ = lean_dbg_sleep(v_ms_boxed_58_, v_f_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessage(lean_object* v_modName_63_, lean_object* v_line_64_, lean_object* v_col_65_, lean_object* v_msg_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_67_ = ((lean_object*)(l_mkPanicMessage___closed__0));
v___x_68_ = lean_string_append(v___x_67_, v_modName_63_);
v___x_69_ = ((lean_object*)(l_mkPanicMessage___closed__1));
v___x_70_ = lean_string_append(v___x_68_, v___x_69_);
v___x_71_ = l_Nat_reprFast(v_line_64_);
v___x_72_ = lean_string_append(v___x_70_, v___x_71_);
lean_dec_ref(v___x_71_);
v___x_73_ = lean_string_append(v___x_72_, v___x_69_);
v___x_74_ = l_Nat_reprFast(v_col_65_);
v___x_75_ = lean_string_append(v___x_73_, v___x_74_);
lean_dec_ref(v___x_74_);
v___x_76_ = ((lean_object*)(l_mkPanicMessage___closed__2));
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
v___x_78_ = lean_string_append(v___x_77_, v_msg_66_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessage___boxed(lean_object* v_modName_79_, lean_object* v_line_80_, lean_object* v_col_81_, lean_object* v_msg_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_mkPanicMessage(v_modName_79_, v_line_80_, v_col_81_, v_msg_82_);
lean_dec_ref(v_msg_82_);
lean_dec_ref(v_modName_79_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___redArg(lean_object* v_inst_84_, lean_object* v_modName_85_, lean_object* v_line_86_, lean_object* v_col_87_, lean_object* v_msg_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = l_mkPanicMessage(v_modName_85_, v_line_86_, v_col_87_, v_msg_88_);
v___x_90_ = l_panic___redArg(v_inst_84_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___redArg___boxed(lean_object* v_inst_91_, lean_object* v_modName_92_, lean_object* v_line_93_, lean_object* v_col_94_, lean_object* v_msg_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_panicWithPos___redArg(v_inst_91_, v_modName_92_, v_line_93_, v_col_94_, v_msg_95_);
lean_dec_ref(v_msg_95_);
lean_dec_ref(v_modName_92_);
lean_dec(v_inst_91_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_modName_99_, lean_object* v_line_100_, lean_object* v_col_101_, lean_object* v_msg_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = l_mkPanicMessage(v_modName_99_, v_line_100_, v_col_101_, v_msg_102_);
v___x_104_ = l_panic___redArg(v_inst_98_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_panicWithPos___boxed(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_, lean_object* v_modName_107_, lean_object* v_line_108_, lean_object* v_col_109_, lean_object* v_msg_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_panicWithPos(v_00_u03b1_105_, v_inst_106_, v_modName_107_, v_line_108_, v_col_109_, v_msg_110_);
lean_dec_ref(v_msg_110_);
lean_dec_ref(v_modName_107_);
lean_dec(v_inst_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessageWithDecl(lean_object* v_modName_113_, lean_object* v_declName_114_, lean_object* v_line_115_, lean_object* v_col_116_, lean_object* v_msg_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_118_ = ((lean_object*)(l_mkPanicMessage___closed__0));
v___x_119_ = lean_string_append(v___x_118_, v_declName_114_);
v___x_120_ = ((lean_object*)(l_mkPanicMessageWithDecl___closed__0));
v___x_121_ = lean_string_append(v___x_119_, v___x_120_);
v___x_122_ = lean_string_append(v___x_121_, v_modName_113_);
v___x_123_ = ((lean_object*)(l_mkPanicMessage___closed__1));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = l_Nat_reprFast(v_line_115_);
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = lean_string_append(v___x_126_, v___x_123_);
v___x_128_ = l_Nat_reprFast(v_col_116_);
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
lean_dec_ref(v___x_128_);
v___x_130_ = ((lean_object*)(l_mkPanicMessage___closed__2));
v___x_131_ = lean_string_append(v___x_129_, v___x_130_);
v___x_132_ = lean_string_append(v___x_131_, v_msg_117_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_mkPanicMessageWithDecl___boxed(lean_object* v_modName_133_, lean_object* v_declName_134_, lean_object* v_line_135_, lean_object* v_col_136_, lean_object* v_msg_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_mkPanicMessageWithDecl(v_modName_133_, v_declName_134_, v_line_135_, v_col_136_, v_msg_137_);
lean_dec_ref(v_msg_137_);
lean_dec_ref(v_declName_134_);
lean_dec_ref(v_modName_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___redArg(lean_object* v_inst_139_, lean_object* v_modName_140_, lean_object* v_declName_141_, lean_object* v_line_142_, lean_object* v_col_143_, lean_object* v_msg_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = l_mkPanicMessageWithDecl(v_modName_140_, v_declName_141_, v_line_142_, v_col_143_, v_msg_144_);
v___x_146_ = l_panic___redArg(v_inst_139_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___redArg___boxed(lean_object* v_inst_147_, lean_object* v_modName_148_, lean_object* v_declName_149_, lean_object* v_line_150_, lean_object* v_col_151_, lean_object* v_msg_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_panicWithPosWithDecl___redArg(v_inst_147_, v_modName_148_, v_declName_149_, v_line_150_, v_col_151_, v_msg_152_);
lean_dec_ref(v_msg_152_);
lean_dec_ref(v_declName_149_);
lean_dec_ref(v_modName_148_);
lean_dec(v_inst_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_modName_156_, lean_object* v_declName_157_, lean_object* v_line_158_, lean_object* v_col_159_, lean_object* v_msg_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_mkPanicMessageWithDecl(v_modName_156_, v_declName_157_, v_line_158_, v_col_159_, v_msg_160_);
v___x_162_ = l_panic___redArg(v_inst_155_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_panicWithPosWithDecl___boxed(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_modName_165_, lean_object* v_declName_166_, lean_object* v_line_167_, lean_object* v_col_168_, lean_object* v_msg_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_panicWithPosWithDecl(v_00_u03b1_163_, v_inst_164_, v_modName_165_, v_declName_166_, v_line_167_, v_col_168_, v_msg_169_);
lean_dec_ref(v_msg_169_);
lean_dec_ref(v_declName_166_);
lean_dec_ref(v_modName_165_);
lean_dec(v_inst_164_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_ptrAddrUnsafe___boxed(lean_object* v_00_u03b1_173_, lean_object* v_a_174_){
_start:
{
size_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = lean_ptr_addr(v_a_174_);
lean_dec(v_a_174_);
v_r_176_ = lean_box_usize(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_isExclusiveUnsafe___boxed(lean_object* v_00_u03b1_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = lean_is_exclusive_obj(v_a_180_);
lean_dec(v_a_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___redArg(lean_object* v_a_183_, lean_object* v_k_184_){
_start:
{
size_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_ptr_addr(v_a_183_);
v___x_186_ = lean_box_usize(v___x_185_);
v___x_187_ = lean_apply_1(v_k_184_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___redArg___boxed(lean_object* v_a_188_, lean_object* v_k_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_withPtrAddrUnsafe___redArg(v_a_188_, v_k_189_);
lean_dec(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_a_193_, lean_object* v_k_194_, lean_object* v_h_195_){
_start:
{
size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_ptr_addr(v_a_193_);
v___x_197_ = lean_box_usize(v___x_196_);
v___x_198_ = lean_apply_1(v_k_194_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_withPtrAddrUnsafe___boxed(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_a_201_, lean_object* v_k_202_, lean_object* v_h_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_withPtrAddrUnsafe(v_00_u03b1_199_, v_00_u03b2_200_, v_a_201_, v_k_202_, v_h_203_);
lean_dec(v_a_201_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_ptrEq___redArg(lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
size_t v___x_207_; size_t v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_ptr_addr(v_a_205_);
v___x_208_ = lean_ptr_addr(v_b_206_);
v___x_209_ = lean_usize_dec_eq(v___x_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_ptrEq___redArg___boxed(lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_ptrEq___redArg(v_a_210_, v_b_211_);
lean_dec(v_b_211_);
lean_dec(v_a_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_ptrEq(lean_object* v_00_u03b1_214_, lean_object* v_a_215_, lean_object* v_b_216_){
_start:
{
size_t v___x_217_; size_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_ptr_addr(v_a_215_);
v___x_218_ = lean_ptr_addr(v_b_216_);
v___x_219_ = lean_usize_dec_eq(v___x_217_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_ptrEq___boxed(lean_object* v_00_u03b1_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_ptrEq(v_00_u03b1_220_, v_a_221_, v_b_222_);
lean_dec(v_b_222_);
lean_dec(v_a_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_ptrEqList___redArg(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
if (lean_obj_tag(v_x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 1;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
else
{
if (lean_obj_tag(v_x_226_) == 1)
{
lean_object* v_head_229_; lean_object* v_tail_230_; lean_object* v_head_231_; lean_object* v_tail_232_; size_t v___x_233_; size_t v___x_234_; uint8_t v___x_235_; 
v_head_229_ = lean_ctor_get(v_x_225_, 0);
v_tail_230_ = lean_ctor_get(v_x_225_, 1);
v_head_231_ = lean_ctor_get(v_x_226_, 0);
v_tail_232_ = lean_ctor_get(v_x_226_, 1);
v___x_233_ = lean_ptr_addr(v_head_229_);
v___x_234_ = lean_ptr_addr(v_head_231_);
v___x_235_ = lean_usize_dec_eq(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
return v___x_235_;
}
else
{
v_x_225_ = v_tail_230_;
v_x_226_ = v_tail_232_;
goto _start;
}
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_ptrEqList___redArg___boxed(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_ptrEqList___redArg(v_x_238_, v_x_239_);
lean_dec(v_x_239_);
lean_dec(v_x_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_ptrEqList(lean_object* v_00_u03b1_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_ptrEqList___redArg(v_x_243_, v_x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_ptrEqList___boxed(lean_object* v_00_u03b1_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_ptrEqList(v_00_u03b1_246_, v_x_247_, v_x_248_);
lean_dec(v_x_248_);
lean_dec(v_x_247_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_withPtrEqUnsafe___redArg(lean_object* v_a_251_, lean_object* v_b_252_, lean_object* v_k_253_){
_start:
{
size_t v___x_254_; size_t v___x_255_; uint8_t v___x_256_; 
v___x_254_ = lean_ptr_addr(v_a_251_);
v___x_255_ = lean_ptr_addr(v_b_252_);
v___x_256_ = lean_usize_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_1(v_k_253_, v___x_257_);
v___x_259_ = lean_unbox(v___x_258_);
return v___x_259_;
}
else
{
lean_dec_ref(v_k_253_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___redArg___boxed(lean_object* v_a_260_, lean_object* v_b_261_, lean_object* v_k_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_withPtrEqUnsafe___redArg(v_a_260_, v_b_261_, v_k_262_);
lean_dec(v_b_261_);
lean_dec(v_a_260_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT uint8_t l_withPtrEqUnsafe(lean_object* v_00_u03b1_265_, lean_object* v_a_266_, lean_object* v_b_267_, lean_object* v_k_268_, lean_object* v_h_269_){
_start:
{
size_t v___x_270_; size_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_ptr_addr(v_a_266_);
v___x_271_ = lean_ptr_addr(v_b_267_);
v___x_272_ = lean_usize_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_apply_1(v_k_268_, v___x_273_);
v___x_275_ = lean_unbox(v___x_274_);
return v___x_275_;
}
else
{
lean_dec_ref(v_k_268_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_withPtrEqUnsafe___boxed(lean_object* v_00_u03b1_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_k_279_, lean_object* v_h_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_withPtrEqUnsafe(v_00_u03b1_276_, v_a_277_, v_b_278_, v_k_279_, v_h_280_);
lean_dec(v_b_278_);
lean_dec(v_a_277_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l_withPtrEqDecEq___redArg(lean_object* v_a_283_, lean_object* v_b_284_, lean_object* v_k_285_){
_start:
{
size_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_ptr_addr(v_a_283_);
v___x_287_ = lean_ptr_addr(v_b_284_);
v___x_288_ = lean_usize_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_k_285_, v___x_289_);
v___x_291_ = lean_unbox(v___x_290_);
return v___x_291_;
}
else
{
lean_dec_ref(v_k_285_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___redArg___boxed(lean_object* v_a_292_, lean_object* v_b_293_, lean_object* v_k_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_withPtrEqDecEq___redArg(v_a_292_, v_b_293_, v_k_294_);
lean_dec(v_b_293_);
lean_dec(v_a_292_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT uint8_t l_withPtrEqDecEq(lean_object* v_00_u03b1_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v_k_300_){
_start:
{
size_t v___x_301_; size_t v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_ptr_addr(v_a_298_);
v___x_302_ = lean_ptr_addr(v_b_299_);
v___x_303_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_k_300_, v___x_304_);
v___x_306_ = lean_unbox(v___x_305_);
return v___x_306_;
}
else
{
lean_dec_ref(v_k_300_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_withPtrEqDecEq___boxed(lean_object* v_00_u03b1_307_, lean_object* v_a_308_, lean_object* v_b_309_, lean_object* v_k_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_withPtrEqDecEq(v_00_u03b1_307_, v_a_308_, v_b_309_, v_k_310_);
lean_dec(v_b_309_);
lean_dec(v_a_308_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
