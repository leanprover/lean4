// Lean compiler output
// Module: Std.Http.Internal.String
// Imports: import Init.Grind public import Init.Data.String.TakeDrop public import Std.Http.Internal.Char import Init.Data.String.Csimp
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_toListImpl(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static const lean_string_object l_Std_Http_Internal_quoteCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Internal_quoteCore___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_quoteCore___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Internal_quoteCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\\"};
static const lean_object* l_Std_Http_Internal_quoteCore___redArg___closed__1 = (const lean_object*)&l_Std_Http_Internal_quoteCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___redArg(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1___boxed(lean_object*);
static const lean_string_object l_Std_Http_Internal_quoteHttpString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Std_Http_Internal_quoteHttpString___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Internal_quoteHttpString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Http.Internal.String"};
static const lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__0 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Internal_quoteHttpString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Http.Internal.quoteHttpString!"};
static const lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__1 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x21___closed__1_value;
static const lean_string_object l_Std_Http_Internal_quoteHttpString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "invalid HTTP quoted-string content"};
static const lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__2 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x21___closed__2_value;
static lean_once_cell_t l_Std_Http_Internal_quoteHttpString_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_isToken_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object*);
lean_object* l_Std_Http_Internal_quoteCore___redArg(uint32_t v_c_3_){
_start:
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 9;
v___x_23_ = lean_uint32_dec_eq(v_c_3_, v___x_22_);
if (v___x_23_ == 0)
{
uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 32;
v___x_25_ = lean_uint32_dec_eq(v_c_3_, v___x_24_);
if (v___x_25_ == 0)
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 33;
v___x_27_ = lean_uint32_dec_eq(v_c_3_, v___x_26_);
if (v___x_27_ == 0)
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 35;
v___x_29_ = lean_uint32_dec_le(v___x_28_, v_c_3_);
if (v___x_29_ == 0)
{
goto v___jp_17_;
}
else
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 91;
v___x_31_ = lean_uint32_dec_le(v_c_3_, v___x_30_);
if (v___x_31_ == 0)
{
goto v___jp_17_;
}
else
{
goto v___jp_4_;
}
}
}
else
{
goto v___jp_4_;
}
}
else
{
goto v___jp_4_;
}
}
else
{
goto v___jp_4_;
}
v___jp_4_:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_6_ = lean_string_push(v___x_5_, v_c_3_);
return v___x_6_;
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__1));
v___x_9_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_10_ = lean_string_push(v___x_9_, v_c_3_);
v___x_11_ = lean_string_append(v___x_8_, v___x_10_);
lean_dec_ref(v___x_10_);
return v___x_11_;
}
v___jp_12_:
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 34;
v___x_14_ = lean_uint32_dec_eq(v_c_3_, v___x_13_);
if (v___x_14_ == 0)
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 92;
v___x_16_ = lean_uint32_dec_eq(v_c_3_, v___x_15_);
goto v___jp_7_;
}
else
{
goto v___jp_7_;
}
}
v___jp_17_:
{
uint32_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = 93;
v___x_19_ = lean_uint32_dec_le(v___x_18_, v_c_3_);
if (v___x_19_ == 0)
{
goto v___jp_12_;
}
else
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 126;
v___x_21_ = lean_uint32_dec_le(v_c_3_, v___x_20_);
if (v___x_21_ == 0)
{
goto v___jp_12_;
}
else
{
goto v___jp_4_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_quoteCore___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_3_ = stack[0].m_num;
lean_object* v_res_32_;
v_res_32_ = l_Std_Http_Internal_quoteCore___redArg(v_c_3_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___redArg___boxed(lean_object* v_c_33_){
_start:
{
uint32_t v_c_boxed_34_; lean_object* v_res_35_; 
v_c_boxed_34_ = lean_unbox_uint32(v_c_33_);
lean_dec(v_c_33_);
v_res_35_ = l_Std_Http_Internal_quoteCore___redArg(v_c_boxed_34_);
return v_res_35_;
}
}
lean_object* l_Std_Http_Internal_quoteCore(uint32_t v_c_36_, lean_object* v_h_u2080_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Std_Http_Internal_quoteCore___redArg(v_c_36_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Std_Http_Internal_quoteCore_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_36_ = stack[0].m_num;
lean_object* v_res_39_;
v_res_39_ = l_Std_Http_Internal_quoteCore(v_c_36_, lean_box(0));
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___boxed(lean_object* v_c_40_, lean_object* v_h_u2080_41_){
_start:
{
uint32_t v_c_boxed_42_; lean_object* v_res_43_; 
v_c_boxed_42_ = lean_unbox_uint32(v_c_40_);
lean_dec(v_c_40_);
v_res_43_ = l_Std_Http_Internal_quoteCore(v_c_boxed_42_, v_h_u2080_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
return v_x_44_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; uint32_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_head_46_ = lean_ctor_get(v_x_45_, 0);
v_tail_47_ = lean_ctor_get(v_x_45_, 1);
v___x_48_ = lean_unbox_uint32(v_head_46_);
v___x_49_ = l_Std_Http_Internal_quoteCore___redArg(v___x_48_);
v___x_50_ = lean_string_append(v_x_44_, v___x_49_);
lean_dec_ref(v___x_49_);
v_x_44_ = v___x_50_;
v_x_45_ = v_tail_47_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v_x_52_, v_x_53_);
lean_dec(v_x_53_);
return v_res_54_;
}
}
uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v_tail_58_; uint32_t v___x_75_; uint32_t v___x_76_; uint8_t v___x_77_; 
v_head_57_ = lean_ctor_get(v_x_55_, 0);
v_tail_58_ = lean_ctor_get(v_x_55_, 1);
v___x_75_ = 33;
v___x_76_ = lean_unbox_uint32(v_head_57_);
v___x_77_ = lean_uint32_dec_eq(v___x_76_, v___x_75_);
if (v___x_77_ == 0)
{
uint32_t v___x_78_; uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_78_ = 35;
v___x_79_ = lean_unbox_uint32(v_head_57_);
v___x_80_ = lean_uint32_dec_eq(v___x_79_, v___x_78_);
if (v___x_80_ == 0)
{
uint32_t v___x_81_; uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_81_ = 36;
v___x_82_ = lean_unbox_uint32(v_head_57_);
v___x_83_ = lean_uint32_dec_eq(v___x_82_, v___x_81_);
if (v___x_83_ == 0)
{
uint32_t v___x_84_; uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_84_ = 37;
v___x_85_ = lean_unbox_uint32(v_head_57_);
v___x_86_ = lean_uint32_dec_eq(v___x_85_, v___x_84_);
if (v___x_86_ == 0)
{
uint32_t v___x_87_; uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_87_ = 38;
v___x_88_ = lean_unbox_uint32(v_head_57_);
v___x_89_ = lean_uint32_dec_eq(v___x_88_, v___x_87_);
if (v___x_89_ == 0)
{
uint32_t v___x_90_; uint32_t v___x_91_; uint8_t v___x_92_; 
v___x_90_ = 39;
v___x_91_ = lean_unbox_uint32(v_head_57_);
v___x_92_ = lean_uint32_dec_eq(v___x_91_, v___x_90_);
if (v___x_92_ == 0)
{
uint32_t v___x_93_; uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = 42;
v___x_94_ = lean_unbox_uint32(v_head_57_);
v___x_95_ = lean_uint32_dec_eq(v___x_94_, v___x_93_);
if (v___x_95_ == 0)
{
uint32_t v___x_96_; uint32_t v___x_97_; uint8_t v___x_98_; 
v___x_96_ = 43;
v___x_97_ = lean_unbox_uint32(v_head_57_);
v___x_98_ = lean_uint32_dec_eq(v___x_97_, v___x_96_);
if (v___x_98_ == 0)
{
uint32_t v___x_99_; uint32_t v___x_100_; uint8_t v___x_101_; 
v___x_99_ = 45;
v___x_100_ = lean_unbox_uint32(v_head_57_);
v___x_101_ = lean_uint32_dec_eq(v___x_100_, v___x_99_);
if (v___x_101_ == 0)
{
uint32_t v___x_102_; uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_102_ = 46;
v___x_103_ = lean_unbox_uint32(v_head_57_);
v___x_104_ = lean_uint32_dec_eq(v___x_103_, v___x_102_);
if (v___x_104_ == 0)
{
uint32_t v___x_105_; uint32_t v___x_106_; uint8_t v___x_107_; 
v___x_105_ = 94;
v___x_106_ = lean_unbox_uint32(v_head_57_);
v___x_107_ = lean_uint32_dec_eq(v___x_106_, v___x_105_);
if (v___x_107_ == 0)
{
uint32_t v___x_108_; uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_108_ = 95;
v___x_109_ = lean_unbox_uint32(v_head_57_);
v___x_110_ = lean_uint32_dec_eq(v___x_109_, v___x_108_);
if (v___x_110_ == 0)
{
uint32_t v___x_111_; uint32_t v___x_112_; uint8_t v___x_113_; 
v___x_111_ = 96;
v___x_112_ = lean_unbox_uint32(v_head_57_);
v___x_113_ = lean_uint32_dec_eq(v___x_112_, v___x_111_);
if (v___x_113_ == 0)
{
uint32_t v___x_114_; uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_114_ = 124;
v___x_115_ = lean_unbox_uint32(v_head_57_);
v___x_116_ = lean_uint32_dec_eq(v___x_115_, v___x_114_);
if (v___x_116_ == 0)
{
uint32_t v___x_117_; uint32_t v___x_118_; uint8_t v___x_119_; 
v___x_117_ = 126;
v___x_118_ = lean_unbox_uint32(v_head_57_);
v___x_119_ = lean_uint32_dec_eq(v___x_118_, v___x_117_);
if (v___x_119_ == 0)
{
uint32_t v___x_120_; uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = 48;
v___x_121_ = lean_unbox_uint32(v_head_57_);
v___x_122_ = lean_uint32_dec_le(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
goto v___jp_67_;
}
else
{
uint32_t v___x_123_; uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_123_ = 57;
v___x_124_ = lean_unbox_uint32(v_head_57_);
v___x_125_ = lean_uint32_dec_le(v___x_124_, v___x_123_);
if (v___x_125_ == 0)
{
goto v___jp_67_;
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
v___jp_59_:
{
uint32_t v___x_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_60_ = 97;
v___x_61_ = lean_unbox_uint32(v_head_57_);
v___x_62_ = lean_uint32_dec_le(v___x_60_, v___x_61_);
if (v___x_62_ == 0)
{
return v___x_62_;
}
else
{
uint32_t v___x_63_; uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_63_ = 122;
v___x_64_ = lean_unbox_uint32(v_head_57_);
v___x_65_ = lean_uint32_dec_le(v___x_64_, v___x_63_);
if (v___x_65_ == 0)
{
return v___x_65_;
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
}
v___jp_67_:
{
uint32_t v___x_68_; uint32_t v___x_69_; uint8_t v___x_70_; 
v___x_68_ = 65;
v___x_69_ = lean_unbox_uint32(v_head_57_);
v___x_70_ = lean_uint32_dec_le(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
goto v___jp_59_;
}
else
{
uint32_t v___x_71_; uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = 90;
v___x_72_ = lean_unbox_uint32(v_head_57_);
v___x_73_ = lean_uint32_dec_le(v___x_72_, v___x_71_);
if (v___x_73_ == 0)
{
goto v___jp_59_;
}
else
{
v_x_55_ = v_tail_58_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_55_ = stack[0].m_obj;
uint8_t v_res_142_;
v_res_142_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_x_55_);
stack->m_num = v_res_142_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1___boxed(lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_x_143_);
lean_dec(v_x_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object* v_s_147_){
_start:
{
lean_object* v_sl_148_; uint8_t v___y_154_; uint8_t v___x_155_; 
lean_inc_ref(v_s_147_);
v_sl_148_ = l_String_toListImpl(v_s_147_);
v___x_155_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_sl_148_);
if (v___x_155_ == 0)
{
v___y_154_ = v___x_155_;
goto v___jp_153_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = l_List_isEmpty___redArg(v_sl_148_);
if (v___x_156_ == 0)
{
v___y_154_ = v___x_155_;
goto v___jp_153_;
}
else
{
lean_dec_ref(v_s_147_);
goto v___jp_149_;
}
}
v___jp_149_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString___redArg___closed__0));
v___x_151_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v___x_150_, v_sl_148_);
lean_dec(v_sl_148_);
v___x_152_ = lean_string_append(v___x_151_, v___x_150_);
return v___x_152_;
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
lean_dec_ref(v_s_147_);
goto v___jp_149_;
}
else
{
lean_dec(v_sl_148_);
return v_s_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object* v_s_157_, lean_object* v_h_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_157_);
return v___x_159_;
}
}
uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = 1;
return v___x_161_;
}
else
{
lean_object* v_head_162_; lean_object* v_tail_163_; uint32_t v___x_188_; uint32_t v___x_189_; uint8_t v___x_190_; 
v_head_162_ = lean_ctor_get(v_x_160_, 0);
v_tail_163_ = lean_ctor_get(v_x_160_, 1);
v___x_188_ = 9;
v___x_189_ = lean_unbox_uint32(v_head_162_);
v___x_190_ = lean_uint32_dec_eq(v___x_189_, v___x_188_);
if (v___x_190_ == 0)
{
uint32_t v___x_191_; uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_191_ = 32;
v___x_192_ = lean_unbox_uint32(v_head_162_);
v___x_193_ = lean_uint32_dec_eq(v___x_192_, v___x_191_);
if (v___x_193_ == 0)
{
uint32_t v___x_194_; uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = 33;
v___x_195_ = lean_unbox_uint32(v_head_162_);
v___x_196_ = lean_uint32_dec_eq(v___x_195_, v___x_194_);
if (v___x_196_ == 0)
{
uint32_t v___x_197_; uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_197_ = 35;
v___x_198_ = lean_unbox_uint32(v_head_162_);
v___x_199_ = lean_uint32_dec_le(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
goto v___jp_180_;
}
else
{
uint32_t v___x_200_; uint32_t v___x_201_; uint8_t v___x_202_; 
v___x_200_ = 91;
v___x_201_ = lean_unbox_uint32(v_head_162_);
v___x_202_ = lean_uint32_dec_le(v___x_201_, v___x_200_);
if (v___x_202_ == 0)
{
goto v___jp_180_;
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
v___jp_164_:
{
uint32_t v___x_165_; uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_165_ = 9;
v___x_166_ = lean_unbox_uint32(v_head_162_);
v___x_167_ = lean_uint32_dec_eq(v___x_166_, v___x_165_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = 32;
v___x_169_ = lean_unbox_uint32(v_head_162_);
v___x_170_ = lean_uint32_dec_eq(v___x_169_, v___x_168_);
if (v___x_170_ == 0)
{
uint32_t v___x_171_; uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_171_ = 33;
v___x_172_ = lean_unbox_uint32(v_head_162_);
v___x_173_ = lean_uint32_dec_le(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
uint32_t v___x_174_; uint32_t v___x_175_; uint8_t v___x_176_; 
v___x_174_ = 126;
v___x_175_ = lean_unbox_uint32(v_head_162_);
v___x_176_ = lean_uint32_dec_le(v___x_175_, v___x_174_);
if (v___x_176_ == 0)
{
return v___x_176_;
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
v___jp_180_:
{
uint32_t v___x_181_; uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = 93;
v___x_182_ = lean_unbox_uint32(v_head_162_);
v___x_183_ = lean_uint32_dec_le(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
goto v___jp_164_;
}
else
{
uint32_t v___x_184_; uint32_t v___x_185_; uint8_t v___x_186_; 
v___x_184_ = 126;
v___x_185_ = lean_unbox_uint32(v_head_162_);
v___x_186_ = lean_uint32_dec_le(v___x_185_, v___x_184_);
if (v___x_186_ == 0)
{
goto v___jp_164_;
}
else
{
v_x_160_ = v_tail_163_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_160_ = stack[0].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_160_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(lean_object* v_x_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_208_);
lean_dec(v_x_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object* v_s_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
lean_inc_ref(v_s_211_);
v___x_212_ = l_String_toListImpl(v_s_211_);
v___x_213_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v___x_212_);
lean_dec(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_dec_ref(v_s_211_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_211_);
v___x_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object* v_msg_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_219_ = lean_panic_fn_borrowed(v___x_218_, v_msg_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_223_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__2));
v___x_224_ = lean_unsigned_to_nat(12u);
v___x_225_ = lean_unsigned_to_nat(84u);
v___x_226_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__1));
v___x_227_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__0));
v___x_228_ = l_mkPanicMessageWithDecl(v___x_227_, v___x_226_, v___x_225_, v___x_224_, v___x_223_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object* v_s_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_obj_once(&l_Std_Http_Internal_quoteHttpString_x21___closed__3, &l_Std_Http_Internal_quoteHttpString_x21___closed__3_once, _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3);
v___x_232_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; 
v_val_233_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_230_, 1);
return v_val_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_tag_nat(v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl___boxed(lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(v_x_236_);
lean_dec(v_x_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object* v_t_238_, lean_object* v_k_239_){
_start:
{
switch(lean_obj_tag(v_t_238_))
{
case 1:
{
uint8_t v_escaped_240_; lean_object* v_acc_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_escaped_240_ = lean_ctor_get_uint8(v_t_238_, sizeof(void*)*1);
v_acc_241_ = lean_ctor_get(v_t_238_, 0);
lean_inc_ref(v_acc_241_);
lean_dec_ref_known(v_t_238_, 1);
v___x_242_ = lean_box(v_escaped_240_);
v___x_243_ = lean_apply_2(v_k_239_, v___x_242_, v_acc_241_);
return v___x_243_;
}
case 2:
{
lean_object* v_result_244_; lean_object* v___x_245_; 
v_result_244_ = lean_ctor_get(v_t_238_, 0);
lean_inc_ref(v_result_244_);
lean_dec_ref_known(v_t_238_, 1);
v___x_245_ = lean_apply_1(v_k_239_, v_result_244_);
return v___x_245_;
}
default: 
{
lean_dec(v_t_238_);
return v_k_239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object* v_motive_246_, lean_object* v_ctorIdx_247_, lean_object* v_t_248_, lean_object* v_h_249_, lean_object* v_k_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_248_, v_k_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object* v_motive_252_, lean_object* v_ctorIdx_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_k_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(v_motive_252_, v_ctorIdx_253_, v_t_254_, v_h_255_, v_k_256_);
lean_dec(v_ctorIdx_253_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object* v_t_258_, lean_object* v_start_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_258_, v_start_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object* v_motive_261_, lean_object* v_t_262_, lean_object* v_h_263_, lean_object* v_start_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_262_, v_start_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object* v_t_266_, lean_object* v_valid_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_266_, v_valid_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object* v_motive_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_valid_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_270_, v_valid_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object* v_t_274_, lean_object* v_done_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_274_, v_done_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_done_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_278_, v_done_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object* v_t_282_, lean_object* v_invalid_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_282_, v_invalid_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object* v_motive_285_, lean_object* v_t_286_, lean_object* v_h_287_, lean_object* v_invalid_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_286_, v_invalid_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object* v_s_290_, lean_object* v_pos_291_){
_start:
{
lean_object* v_str_292_; lean_object* v_startInclusive_293_; lean_object* v_endExclusive_294_; lean_object* v___x_295_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v_decide_306_; 
v_str_292_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_293_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_294_ = lean_ctor_get(v_s_290_, 2);
v___x_295_ = lean_nat_add(v_startInclusive_293_, v_pos_291_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_sub(v_endExclusive_294_, v___x_295_);
v_decide_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
lean_dec(v___x_305_);
if (v_decide_306_ == 0)
{
uint32_t v___x_307_; uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_307_ = lean_string_utf8_get_fast(v_str_292_, v___x_295_);
v___x_318_ = 33;
v___x_319_ = lean_uint32_dec_eq(v___x_307_, v___x_318_);
if (v___x_319_ == 0)
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 35;
v___x_321_ = lean_uint32_dec_eq(v___x_307_, v___x_320_);
if (v___x_321_ == 0)
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 36;
v___x_323_ = lean_uint32_dec_eq(v___x_307_, v___x_322_);
if (v___x_323_ == 0)
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 37;
v___x_325_ = lean_uint32_dec_eq(v___x_307_, v___x_324_);
if (v___x_325_ == 0)
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 38;
v___x_327_ = lean_uint32_dec_eq(v___x_307_, v___x_326_);
if (v___x_327_ == 0)
{
uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 39;
v___x_329_ = lean_uint32_dec_eq(v___x_307_, v___x_328_);
if (v___x_329_ == 0)
{
uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 42;
v___x_331_ = lean_uint32_dec_eq(v___x_307_, v___x_330_);
if (v___x_331_ == 0)
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 43;
v___x_333_ = lean_uint32_dec_eq(v___x_307_, v___x_332_);
if (v___x_333_ == 0)
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 45;
v___x_335_ = lean_uint32_dec_eq(v___x_307_, v___x_334_);
if (v___x_335_ == 0)
{
uint32_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = 46;
v___x_337_ = lean_uint32_dec_eq(v___x_307_, v___x_336_);
if (v___x_337_ == 0)
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 94;
v___x_339_ = lean_uint32_dec_eq(v___x_307_, v___x_338_);
if (v___x_339_ == 0)
{
uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 95;
v___x_341_ = lean_uint32_dec_eq(v___x_307_, v___x_340_);
if (v___x_341_ == 0)
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 96;
v___x_343_ = lean_uint32_dec_eq(v___x_307_, v___x_342_);
if (v___x_343_ == 0)
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 124;
v___x_345_ = lean_uint32_dec_eq(v___x_307_, v___x_344_);
if (v___x_345_ == 0)
{
uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = 126;
v___x_347_ = lean_uint32_dec_eq(v___x_307_, v___x_346_);
if (v___x_347_ == 0)
{
uint32_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = 48;
v___x_349_ = lean_uint32_dec_le(v___x_348_, v___x_307_);
if (v___x_349_ == 0)
{
goto v___jp_313_;
}
else
{
uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 57;
v___x_351_ = lean_uint32_dec_le(v___x_307_, v___x_350_);
if (v___x_351_ == 0)
{
goto v___jp_313_;
}
else
{
goto v___jp_296_;
}
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
}
else
{
goto v___jp_296_;
}
v___jp_308_:
{
uint32_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 97;
v___x_310_ = lean_uint32_dec_le(v___x_309_, v___x_307_);
if (v___x_310_ == 0)
{
lean_dec(v___x_295_);
return v_pos_291_;
}
else
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 122;
v___x_312_ = lean_uint32_dec_le(v___x_307_, v___x_311_);
if (v___x_312_ == 0)
{
lean_dec(v___x_295_);
return v_pos_291_;
}
else
{
goto v___jp_296_;
}
}
}
v___jp_313_:
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 65;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v___x_307_);
if (v___x_315_ == 0)
{
goto v___jp_308_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 90;
v___x_317_ = lean_uint32_dec_le(v___x_307_, v___x_316_);
if (v___x_317_ == 0)
{
goto v___jp_308_;
}
else
{
goto v___jp_296_;
}
}
}
}
else
{
lean_dec(v___x_295_);
return v_pos_291_;
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_297_ = lean_string_utf8_next_fast(v_str_292_, v___x_295_);
v___x_298_ = lean_nat_sub(v___x_297_, v___x_295_);
lean_dec(v___x_295_);
v___x_299_ = lean_nat_add(v_pos_291_, v___x_298_);
lean_dec(v___x_298_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_pos_291_, v___x_300_);
v___x_302_ = lean_nat_dec_le(v___x_301_, v___x_299_);
lean_dec(v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v___x_299_);
return v_pos_291_;
}
else
{
lean_dec(v_pos_291_);
v_pos_291_ = v___x_299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object* v_s_352_, lean_object* v_pos_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v_s_352_, v_pos_353_);
lean_dec_ref(v_s_352_);
return v_res_354_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(lean_object* v___x_355_, lean_object* v___x_356_, uint32_t v___x_357_, lean_object* v___x_358_, lean_object* v_s_359_, lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
uint8_t v_decide_362_; 
v_decide_362_ = lean_nat_dec_eq(v_a_360_, v___x_358_);
if (v_decide_362_ == 0)
{
uint32_t v___x_363_; uint8_t v_decide_364_; uint32_t v___x_365_; lean_object* v___x_366_; 
v___x_363_ = 34;
v_decide_364_ = lean_nat_dec_eq(v___x_355_, v___x_356_);
v___x_365_ = lean_string_utf8_get_fast(v_s_359_, v_a_360_);
v___x_366_ = lean_string_utf8_next_fast(v_s_359_, v_a_360_);
lean_dec(v_a_360_);
switch(lean_obj_tag(v_b_361_))
{
case 0:
{
uint8_t v___x_367_; 
v___x_367_ = lean_uint32_dec_eq(v___x_365_, v___x_363_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(3);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_368_;
goto _start;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_371_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v_decide_364_);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_371_;
goto _start;
}
}
case 1:
{
uint8_t v_escaped_373_; lean_object* v_acc_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_427_; 
v_escaped_373_ = lean_ctor_get_uint8(v_b_361_, sizeof(void*)*1);
v_acc_374_ = lean_ctor_get(v_b_361_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_b_361_);
if (v_isSharedCheck_427_ == 0)
{
v___x_376_ = v_b_361_;
v_isShared_377_ = v_isSharedCheck_427_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_acc_374_);
lean_dec(v_b_361_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_427_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
if (v_escaped_373_ == 0)
{
uint32_t v___x_384_; uint8_t v___x_385_; 
lean_del_object(v___x_376_);
v___x_384_ = 92;
v___x_385_ = lean_uint32_dec_eq(v___x_365_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
v___x_386_ = lean_uint32_dec_eq(v___x_365_, v___x_363_);
if (v___x_386_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 9;
v___x_401_ = lean_uint32_dec_eq(v___x_365_, v___x_400_);
if (v___x_401_ == 0)
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 32;
v___x_403_ = lean_uint32_dec_eq(v___x_365_, v___x_402_);
if (v___x_403_ == 0)
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 33;
v___x_405_ = lean_uint32_dec_eq(v___x_365_, v___x_404_);
if (v___x_405_ == 0)
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 35;
v___x_407_ = lean_uint32_dec_le(v___x_406_, v___x_365_);
if (v___x_407_ == 0)
{
goto v___jp_391_;
}
else
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 91;
v___x_409_ = lean_uint32_dec_le(v___x_365_, v___x_408_);
if (v___x_409_ == 0)
{
goto v___jp_391_;
}
else
{
goto v___jp_387_;
}
}
}
else
{
goto v___jp_387_;
}
}
else
{
goto v___jp_387_;
}
}
else
{
goto v___jp_387_;
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_410_, 0, v_acc_374_);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_410_;
goto _start;
}
v___jp_387_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_string_push(v_acc_374_, v___x_365_);
v___x_389_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_386_);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_389_;
goto _start;
}
v___jp_391_:
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 93;
v___x_393_ = lean_uint32_dec_le(v___x_392_, v___x_365_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v_acc_374_);
v___x_394_ = lean_box(3);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_394_;
goto _start;
}
else
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 126;
v___x_397_ = lean_uint32_dec_le(v___x_365_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_acc_374_);
v___x_398_ = lean_box(3);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_398_;
goto _start;
}
else
{
goto v___jp_387_;
}
}
}
}
else
{
uint8_t v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_uint32_dec_eq(v___x_357_, v___x_363_);
v___x_413_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_413_, 0, v_acc_374_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_412_);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_413_;
goto _start;
}
}
else
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 9;
v___x_416_ = lean_uint32_dec_eq(v___x_365_, v___x_415_);
if (v___x_416_ == 0)
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 32;
v___x_418_ = lean_uint32_dec_eq(v___x_365_, v___x_417_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 33;
v___x_420_ = lean_uint32_dec_le(v___x_419_, v___x_365_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_del_object(v___x_376_);
lean_dec_ref(v_acc_374_);
v___x_421_ = lean_box(3);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_421_;
goto _start;
}
else
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 126;
v___x_424_ = lean_uint32_dec_le(v___x_365_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_del_object(v___x_376_);
lean_dec_ref(v_acc_374_);
v___x_425_ = lean_box(3);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_425_;
goto _start;
}
else
{
goto v___jp_378_;
}
}
}
else
{
goto v___jp_378_;
}
}
else
{
goto v___jp_378_;
}
}
v___jp_378_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_string_push(v_acc_374_, v___x_365_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_379_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v_decide_364_);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_381_;
goto _start;
}
}
}
}
case 2:
{
lean_object* v___x_428_; 
lean_dec_ref_known(v_b_361_, 1);
v___x_428_ = lean_box(3);
v_a_360_ = v___x_366_;
v_b_361_ = v___x_428_;
goto _start;
}
default: 
{
v_a_360_ = v___x_366_;
goto _start;
}
}
}
else
{
lean_dec(v_a_360_);
return v_b_361_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_355_ = stack[0].m_obj;
lean_object* v___x_356_ = stack[1].m_obj;
uint32_t v___x_357_ = stack[2].m_num;
lean_object* v___x_358_ = stack[3].m_obj;
lean_object* v_s_359_ = stack[4].m_obj;
lean_object* v_a_360_ = stack[5].m_obj;
lean_object* v_b_361_ = stack[6].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_355_, v___x_356_, v___x_357_, v___x_358_, v_s_359_, v_a_360_, v_b_361_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v_s_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
uint32_t v___x_2616__boxed_439_; lean_object* v_res_440_; 
v___x_2616__boxed_439_ = lean_unbox_uint32(v___x_434_);
lean_dec(v___x_434_);
v_res_440_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_432_, v___x_433_, v___x_2616__boxed_439_, v___x_435_, v_s_436_, v_a_437_, v_b_438_);
lean_dec_ref(v_s_436_);
lean_dec(v___x_435_);
lean_dec(v___x_433_);
lean_dec(v___x_432_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object* v_s_441_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v_decide_452_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_string_utf8_byte_size(v_s_441_);
v_decide_452_ = lean_nat_dec_eq(v___x_450_, v___x_451_);
if (v_decide_452_ == 0)
{
uint32_t v___x_453_; uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = 34;
v___x_454_ = lean_string_utf8_get_fast(v_s_441_, v___x_450_);
v___x_455_ = lean_uint32_dec_eq(v___x_454_, v___x_453_);
if (v___x_455_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(0);
v___x_457_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_450_, v___x_451_, v___x_454_, v___x_451_, v_s_441_, v___x_450_, v___x_456_);
lean_dec_ref(v_s_441_);
if (lean_obj_tag(v___x_457_) == 2)
{
lean_object* v_result_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_result_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_result_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 1);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_result_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v___x_457_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
}
else
{
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v_decide_447_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_string_utf8_byte_size(v_s_441_);
lean_inc_ref(v_s_441_);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v_s_441_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
v___x_446_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_445_, v___x_443_);
lean_dec_ref_known(v___x_445_, 3);
v_decide_447_ = lean_nat_dec_eq(v___x_446_, v___x_444_);
lean_dec(v___x_446_);
if (v_decide_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec_ref(v_s_441_);
v___x_448_ = lean_box(0);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_s_441_);
return v___x_449_;
}
}
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(lean_object* v___x_467_, lean_object* v___x_468_, lean_object* v___x_469_, uint32_t v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v_s_473_, lean_object* v_inst_474_, lean_object* v_R_475_, lean_object* v_a_476_, lean_object* v_b_477_, lean_object* v_c_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_468_, v___x_469_, v___x_470_, v___x_472_, v_s_473_, v_a_476_, v_b_477_);
return v___x_479_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_467_ = stack[0].m_obj;
lean_object* v___x_468_ = stack[1].m_obj;
lean_object* v___x_469_ = stack[2].m_obj;
uint32_t v___x_470_ = stack[3].m_num;
lean_object* v___x_471_ = stack[4].m_obj;
lean_object* v___x_472_ = stack[5].m_obj;
lean_object* v_s_473_ = stack[6].m_obj;
lean_object* v_a_476_ = stack[9].m_obj;
lean_object* v_b_477_ = stack[10].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_467_, v___x_468_, v___x_469_, v___x_470_, v___x_471_, v___x_472_, v_s_473_, lean_box(0), lean_box(0), v_a_476_, v_b_477_, lean_box(0));
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v_s_487_, lean_object* v_inst_488_, lean_object* v_R_489_, lean_object* v_a_490_, lean_object* v_b_491_, lean_object* v_c_492_){
_start:
{
uint32_t v___x_2920__boxed_493_; lean_object* v_res_494_; 
v___x_2920__boxed_493_ = lean_unbox_uint32(v___x_484_);
lean_dec(v___x_484_);
v_res_494_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_481_, v___x_482_, v___x_483_, v___x_2920__boxed_493_, v___x_485_, v___x_486_, v_s_487_, v_inst_488_, v_R_489_, v_a_490_, v_b_491_, v_c_492_);
lean_dec_ref(v_s_487_);
lean_dec(v___x_486_);
lean_dec_ref(v___x_485_);
lean_dec(v___x_483_);
lean_dec(v___x_482_);
lean_dec_ref(v___x_481_);
return v_res_494_;
}
}
uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
uint8_t v___x_496_; 
v___x_496_ = 1;
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v_tail_498_; uint32_t v___x_515_; uint32_t v___x_516_; uint8_t v___x_517_; 
v_head_497_ = lean_ctor_get(v_x_495_, 0);
v_tail_498_ = lean_ctor_get(v_x_495_, 1);
v___x_515_ = 33;
v___x_516_ = lean_unbox_uint32(v_head_497_);
v___x_517_ = lean_uint32_dec_eq(v___x_516_, v___x_515_);
if (v___x_517_ == 0)
{
uint32_t v___x_518_; uint32_t v___x_519_; uint8_t v___x_520_; 
v___x_518_ = 35;
v___x_519_ = lean_unbox_uint32(v_head_497_);
v___x_520_ = lean_uint32_dec_eq(v___x_519_, v___x_518_);
if (v___x_520_ == 0)
{
uint32_t v___x_521_; uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_521_ = 36;
v___x_522_ = lean_unbox_uint32(v_head_497_);
v___x_523_ = lean_uint32_dec_eq(v___x_522_, v___x_521_);
if (v___x_523_ == 0)
{
uint32_t v___x_524_; uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = 37;
v___x_525_ = lean_unbox_uint32(v_head_497_);
v___x_526_ = lean_uint32_dec_eq(v___x_525_, v___x_524_);
if (v___x_526_ == 0)
{
uint32_t v___x_527_; uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = 38;
v___x_528_ = lean_unbox_uint32(v_head_497_);
v___x_529_ = lean_uint32_dec_eq(v___x_528_, v___x_527_);
if (v___x_529_ == 0)
{
uint32_t v___x_530_; uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = 39;
v___x_531_ = lean_unbox_uint32(v_head_497_);
v___x_532_ = lean_uint32_dec_eq(v___x_531_, v___x_530_);
if (v___x_532_ == 0)
{
uint32_t v___x_533_; uint32_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = 42;
v___x_534_ = lean_unbox_uint32(v_head_497_);
v___x_535_ = lean_uint32_dec_eq(v___x_534_, v___x_533_);
if (v___x_535_ == 0)
{
uint32_t v___x_536_; uint32_t v___x_537_; uint8_t v___x_538_; 
v___x_536_ = 43;
v___x_537_ = lean_unbox_uint32(v_head_497_);
v___x_538_ = lean_uint32_dec_eq(v___x_537_, v___x_536_);
if (v___x_538_ == 0)
{
uint32_t v___x_539_; uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_539_ = 45;
v___x_540_ = lean_unbox_uint32(v_head_497_);
v___x_541_ = lean_uint32_dec_eq(v___x_540_, v___x_539_);
if (v___x_541_ == 0)
{
uint32_t v___x_542_; uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = 46;
v___x_543_ = lean_unbox_uint32(v_head_497_);
v___x_544_ = lean_uint32_dec_eq(v___x_543_, v___x_542_);
if (v___x_544_ == 0)
{
uint32_t v___x_545_; uint32_t v___x_546_; uint8_t v___x_547_; 
v___x_545_ = 94;
v___x_546_ = lean_unbox_uint32(v_head_497_);
v___x_547_ = lean_uint32_dec_eq(v___x_546_, v___x_545_);
if (v___x_547_ == 0)
{
uint32_t v___x_548_; uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = 95;
v___x_549_ = lean_unbox_uint32(v_head_497_);
v___x_550_ = lean_uint32_dec_eq(v___x_549_, v___x_548_);
if (v___x_550_ == 0)
{
uint32_t v___x_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = 96;
v___x_552_ = lean_unbox_uint32(v_head_497_);
v___x_553_ = lean_uint32_dec_eq(v___x_552_, v___x_551_);
if (v___x_553_ == 0)
{
uint32_t v___x_554_; uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = 124;
v___x_555_ = lean_unbox_uint32(v_head_497_);
v___x_556_ = lean_uint32_dec_eq(v___x_555_, v___x_554_);
if (v___x_556_ == 0)
{
uint32_t v___x_557_; uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = 126;
v___x_558_ = lean_unbox_uint32(v_head_497_);
v___x_559_ = lean_uint32_dec_eq(v___x_558_, v___x_557_);
if (v___x_559_ == 0)
{
uint32_t v___x_560_; uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = 48;
v___x_561_ = lean_unbox_uint32(v_head_497_);
v___x_562_ = lean_uint32_dec_le(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
goto v___jp_507_;
}
else
{
uint32_t v___x_563_; uint32_t v___x_564_; uint8_t v___x_565_; 
v___x_563_ = 57;
v___x_564_ = lean_unbox_uint32(v_head_497_);
v___x_565_ = lean_uint32_dec_le(v___x_564_, v___x_563_);
if (v___x_565_ == 0)
{
goto v___jp_507_;
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
v___jp_499_:
{
uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = 97;
v___x_501_ = lean_unbox_uint32(v_head_497_);
v___x_502_ = lean_uint32_dec_le(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
return v___x_502_;
}
else
{
uint32_t v___x_503_; uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = 122;
v___x_504_ = lean_unbox_uint32(v_head_497_);
v___x_505_ = lean_uint32_dec_le(v___x_504_, v___x_503_);
if (v___x_505_ == 0)
{
return v___x_505_;
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
}
v___jp_507_:
{
uint32_t v___x_508_; uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_508_ = 65;
v___x_509_ = lean_unbox_uint32(v_head_497_);
v___x_510_ = lean_uint32_dec_le(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
goto v___jp_499_;
}
else
{
uint32_t v___x_511_; uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = 90;
v___x_512_ = lean_unbox_uint32(v_head_497_);
v___x_513_ = lean_uint32_dec_le(v___x_512_, v___x_511_);
if (v___x_513_ == 0)
{
goto v___jp_499_;
}
else
{
v_x_495_ = v_tail_498_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00Std_Http_Internal_isToken_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_495_ = stack[0].m_obj;
uint8_t v_res_582_;
v_res_582_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_x_495_);
stack->m_num = v_res_582_;
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_isToken_spec__0___boxed(lean_object* v_x_583_){
_start:
{
uint8_t v_res_584_; lean_object* v_r_585_; 
v_res_584_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_x_583_);
lean_dec(v_x_583_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
uint8_t l_Std_Http_Internal_isToken(lean_object* v_s_586_){
_start:
{
lean_object* v_s_587_; uint8_t v___x_588_; 
v_s_587_ = l_String_toListImpl(v_s_586_);
v___x_588_ = l_List_isEmpty___redArg(v_s_587_);
if (v___x_588_ == 0)
{
uint8_t v___x_589_; 
v___x_589_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_s_587_);
lean_dec(v_s_587_);
return v___x_589_;
}
else
{
uint8_t v___x_590_; 
lean_dec(v_s_587_);
v___x_590_ = 0;
return v___x_590_;
}
}
}
LEAN_EXPORT void l_Std_Http_Internal_isToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_586_ = stack[0].m_obj;
uint8_t v_res_591_;
v_res_591_ = l_Std_Http_Internal_isToken(v_s_586_);
stack->m_num = v_res_591_;
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object* v_s_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Std_Http_Internal_isToken(v_s_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal_Char(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Csimp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Csimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Std_Http_Internal_Char(uint8_t builtin);
lean_object* initialize_Init_Data_String_Csimp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Csimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_String(builtin);
}
#ifdef __cplusplus
}
#endif
