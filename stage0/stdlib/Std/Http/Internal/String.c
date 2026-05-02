// Lean compiler output
// Module: Std.Http.Internal.String
// Imports: import Init.Grind public import Init.Data.String.TakeDrop public import Std.Http.Internal.Char
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_data(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_isToken_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___redArg(uint32_t v_c_3_){
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___redArg___boxed(lean_object* v_c_32_){
_start:
{
uint32_t v_c_boxed_33_; lean_object* v_res_34_; 
v_c_boxed_33_ = lean_unbox_uint32(v_c_32_);
lean_dec(v_c_32_);
v_res_34_ = l_Std_Http_Internal_quoteCore___redArg(v_c_boxed_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore(uint32_t v_c_35_, lean_object* v_h_u2080_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Http_Internal_quoteCore___redArg(v_c_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___boxed(lean_object* v_c_38_, lean_object* v_h_u2080_39_){
_start:
{
uint32_t v_c_boxed_40_; lean_object* v_res_41_; 
v_c_boxed_40_ = lean_unbox_uint32(v_c_38_);
lean_dec(v_c_38_);
v_res_41_ = l_Std_Http_Internal_quoteCore(v_c_boxed_40_, v_h_u2080_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
return v_x_42_;
}
else
{
lean_object* v_head_44_; lean_object* v_tail_45_; uint32_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_head_44_ = lean_ctor_get(v_x_43_, 0);
v_tail_45_ = lean_ctor_get(v_x_43_, 1);
v___x_46_ = lean_unbox_uint32(v_head_44_);
v___x_47_ = l_Std_Http_Internal_quoteCore___redArg(v___x_46_);
v___x_48_ = lean_string_append(v_x_42_, v___x_47_);
lean_dec_ref(v___x_47_);
v_x_42_ = v___x_48_;
v_x_43_ = v_tail_45_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v_x_50_, v_x_51_);
lean_dec(v_x_51_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; uint8_t v___y_58_; uint8_t v___y_68_; uint32_t v___x_77_; uint32_t v___x_78_; uint8_t v___x_79_; 
v_head_55_ = lean_ctor_get(v_x_53_, 0);
v_tail_56_ = lean_ctor_get(v_x_53_, 1);
v___x_77_ = 33;
v___x_78_ = lean_unbox_uint32(v_head_55_);
v___x_79_ = lean_uint32_dec_eq(v___x_78_, v___x_77_);
if (v___x_79_ == 0)
{
uint32_t v___x_80_; uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_80_ = 35;
v___x_81_ = lean_unbox_uint32(v_head_55_);
v___x_82_ = lean_uint32_dec_eq(v___x_81_, v___x_80_);
if (v___x_82_ == 0)
{
uint32_t v___x_83_; uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = 36;
v___x_84_ = lean_unbox_uint32(v_head_55_);
v___x_85_ = lean_uint32_dec_eq(v___x_84_, v___x_83_);
if (v___x_85_ == 0)
{
uint32_t v___x_86_; uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_86_ = 37;
v___x_87_ = lean_unbox_uint32(v_head_55_);
v___x_88_ = lean_uint32_dec_eq(v___x_87_, v___x_86_);
if (v___x_88_ == 0)
{
uint32_t v___x_89_; uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_89_ = 38;
v___x_90_ = lean_unbox_uint32(v_head_55_);
v___x_91_ = lean_uint32_dec_eq(v___x_90_, v___x_89_);
if (v___x_91_ == 0)
{
uint32_t v___x_92_; uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_92_ = 39;
v___x_93_ = lean_unbox_uint32(v_head_55_);
v___x_94_ = lean_uint32_dec_eq(v___x_93_, v___x_92_);
if (v___x_94_ == 0)
{
uint32_t v___x_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_95_ = 42;
v___x_96_ = lean_unbox_uint32(v_head_55_);
v___x_97_ = lean_uint32_dec_eq(v___x_96_, v___x_95_);
if (v___x_97_ == 0)
{
uint32_t v___x_98_; uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = 43;
v___x_99_ = lean_unbox_uint32(v_head_55_);
v___x_100_ = lean_uint32_dec_eq(v___x_99_, v___x_98_);
if (v___x_100_ == 0)
{
uint32_t v___x_101_; uint32_t v___x_102_; uint8_t v___x_103_; 
v___x_101_ = 45;
v___x_102_ = lean_unbox_uint32(v_head_55_);
v___x_103_ = lean_uint32_dec_eq(v___x_102_, v___x_101_);
if (v___x_103_ == 0)
{
uint32_t v___x_104_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = 46;
v___x_105_ = lean_unbox_uint32(v_head_55_);
v___x_106_ = lean_uint32_dec_eq(v___x_105_, v___x_104_);
if (v___x_106_ == 0)
{
uint32_t v___x_107_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_107_ = 94;
v___x_108_ = lean_unbox_uint32(v_head_55_);
v___x_109_ = lean_uint32_dec_eq(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
uint32_t v___x_110_; uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_110_ = 95;
v___x_111_ = lean_unbox_uint32(v_head_55_);
v___x_112_ = lean_uint32_dec_eq(v___x_111_, v___x_110_);
if (v___x_112_ == 0)
{
uint32_t v___x_113_; uint32_t v___x_114_; uint8_t v___x_115_; 
v___x_113_ = 96;
v___x_114_ = lean_unbox_uint32(v_head_55_);
v___x_115_ = lean_uint32_dec_eq(v___x_114_, v___x_113_);
if (v___x_115_ == 0)
{
uint32_t v___x_116_; uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_116_ = 124;
v___x_117_ = lean_unbox_uint32(v_head_55_);
v___x_118_ = lean_uint32_dec_eq(v___x_117_, v___x_116_);
if (v___x_118_ == 0)
{
uint32_t v___x_119_; uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_119_ = 126;
v___x_120_ = lean_unbox_uint32(v_head_55_);
v___x_121_ = lean_uint32_dec_eq(v___x_120_, v___x_119_);
if (v___x_121_ == 0)
{
uint32_t v___x_122_; uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_122_ = 48;
v___x_123_ = lean_unbox_uint32(v_head_55_);
v___x_124_ = lean_uint32_dec_le(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
v___y_68_ = v___x_124_;
goto v___jp_67_;
}
else
{
uint32_t v___x_125_; uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_125_ = 57;
v___x_126_ = lean_unbox_uint32(v_head_55_);
v___x_127_ = lean_uint32_dec_le(v___x_126_, v___x_125_);
v___y_68_ = v___x_127_;
goto v___jp_67_;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
v___jp_57_:
{
if (v___y_58_ == 0)
{
return v___y_58_;
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
v___jp_60_:
{
uint32_t v___x_61_; uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_61_ = 97;
v___x_62_ = lean_unbox_uint32(v_head_55_);
v___x_63_ = lean_uint32_dec_le(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
v___y_58_ = v___x_63_;
goto v___jp_57_;
}
else
{
uint32_t v___x_64_; uint32_t v___x_65_; uint8_t v___x_66_; 
v___x_64_ = 122;
v___x_65_ = lean_unbox_uint32(v_head_55_);
v___x_66_ = lean_uint32_dec_le(v___x_65_, v___x_64_);
v___y_58_ = v___x_66_;
goto v___jp_57_;
}
}
v___jp_67_:
{
if (v___y_68_ == 0)
{
uint32_t v___x_69_; uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_69_ = 65;
v___x_70_ = lean_unbox_uint32(v_head_55_);
v___x_71_ = lean_uint32_dec_le(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
goto v___jp_60_;
}
else
{
uint32_t v___x_72_; uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_72_ = 90;
v___x_73_ = lean_unbox_uint32(v_head_55_);
v___x_74_ = lean_uint32_dec_le(v___x_73_, v___x_72_);
if (v___x_74_ == 0)
{
goto v___jp_60_;
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
}
}
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
lean_object* v_sl_148_; uint8_t v___x_153_; 
lean_inc_ref(v_s_147_);
v_sl_148_ = lean_string_data(v_s_147_);
v___x_153_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_sl_148_);
if (v___x_153_ == 0)
{
lean_dec_ref(v_s_147_);
goto v___jp_149_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = l_List_isEmpty___redArg(v_sl_148_);
if (v___x_154_ == 0)
{
lean_dec(v_sl_148_);
return v_s_147_;
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object* v_s_155_, lean_object* v_h_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_155_);
return v___x_157_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
uint8_t v___x_159_; 
v___x_159_ = 1;
return v___x_159_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; uint32_t v___x_186_; uint32_t v___x_187_; uint8_t v___x_188_; 
v_head_160_ = lean_ctor_get(v_x_158_, 0);
v_tail_161_ = lean_ctor_get(v_x_158_, 1);
v___x_186_ = 9;
v___x_187_ = lean_unbox_uint32(v_head_160_);
v___x_188_ = lean_uint32_dec_eq(v___x_187_, v___x_186_);
if (v___x_188_ == 0)
{
uint32_t v___x_189_; uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_189_ = 32;
v___x_190_ = lean_unbox_uint32(v_head_160_);
v___x_191_ = lean_uint32_dec_eq(v___x_190_, v___x_189_);
if (v___x_191_ == 0)
{
uint32_t v___x_192_; uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_192_ = 33;
v___x_193_ = lean_unbox_uint32(v_head_160_);
v___x_194_ = lean_uint32_dec_eq(v___x_193_, v___x_192_);
if (v___x_194_ == 0)
{
uint32_t v___x_195_; uint32_t v___x_196_; uint8_t v___x_197_; 
v___x_195_ = 35;
v___x_196_ = lean_unbox_uint32(v_head_160_);
v___x_197_ = lean_uint32_dec_le(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
goto v___jp_178_;
}
else
{
uint32_t v___x_198_; uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = 91;
v___x_199_ = lean_unbox_uint32(v_head_160_);
v___x_200_ = lean_uint32_dec_le(v___x_199_, v___x_198_);
if (v___x_200_ == 0)
{
goto v___jp_178_;
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
v___jp_162_:
{
uint32_t v___x_163_; uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = 9;
v___x_164_ = lean_unbox_uint32(v_head_160_);
v___x_165_ = lean_uint32_dec_eq(v___x_164_, v___x_163_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = 32;
v___x_167_ = lean_unbox_uint32(v_head_160_);
v___x_168_ = lean_uint32_dec_eq(v___x_167_, v___x_166_);
if (v___x_168_ == 0)
{
uint32_t v___x_169_; uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_169_ = 33;
v___x_170_ = lean_unbox_uint32(v_head_160_);
v___x_171_ = lean_uint32_dec_le(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
uint32_t v___x_172_; uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_172_ = 126;
v___x_173_ = lean_unbox_uint32(v_head_160_);
v___x_174_ = lean_uint32_dec_le(v___x_173_, v___x_172_);
if (v___x_174_ == 0)
{
return v___x_174_;
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
v___jp_178_:
{
uint32_t v___x_179_; uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = 93;
v___x_180_ = lean_unbox_uint32(v_head_160_);
v___x_181_ = lean_uint32_dec_le(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
goto v___jp_162_;
}
else
{
uint32_t v___x_182_; uint32_t v___x_183_; uint8_t v___x_184_; 
v___x_182_ = 126;
v___x_183_ = lean_unbox_uint32(v_head_160_);
v___x_184_ = lean_uint32_dec_le(v___x_183_, v___x_182_);
if (v___x_184_ == 0)
{
goto v___jp_162_;
}
else
{
v_x_158_ = v_tail_161_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_205_);
lean_dec(v_x_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object* v_s_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
lean_inc_ref(v_s_208_);
v___x_209_ = lean_string_data(v_s_208_);
v___x_210_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v___x_209_);
lean_dec(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
lean_dec_ref(v_s_208_);
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_208_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object* v_msg_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_216_ = lean_panic_fn_borrowed(v___x_215_, v_msg_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__2));
v___x_221_ = lean_unsigned_to_nat(12u);
v___x_222_ = lean_unsigned_to_nat(83u);
v___x_223_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__1));
v___x_224_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__0));
v___x_225_ = l_mkPanicMessageWithDecl(v___x_224_, v___x_223_, v___x_222_, v___x_221_, v___x_220_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object* v_s_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Std_Http_Internal_quoteHttpString_x21___closed__3, &l_Std_Http_Internal_quoteHttpString_x21___closed__3_once, _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3);
v___x_229_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v___x_227_);
return v_val_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(lean_object* v_x_231_){
_start:
{
switch(lean_obj_tag(v_x_231_))
{
case 0:
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
return v___x_232_;
}
case 1:
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(1u);
return v___x_233_;
}
case 2:
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(2u);
return v___x_234_;
}
default: 
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(3u);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___boxed(lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(v_x_236_);
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
lean_dec_ref(v_t_238_);
v___x_242_ = lean_box(v_escaped_240_);
v___x_243_ = lean_apply_2(v_k_239_, v___x_242_, v_acc_241_);
return v___x_243_;
}
case 2:
{
lean_object* v_result_244_; lean_object* v___x_245_; 
v_result_244_ = lean_ctor_get(v_t_238_, 0);
lean_inc_ref(v_result_244_);
lean_dec_ref(v_t_238_);
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
lean_object* v_str_292_; lean_object* v_startInclusive_293_; lean_object* v_endExclusive_294_; lean_object* v___x_295_; uint8_t v___y_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_str_292_ = lean_ctor_get(v_s_290_, 0);
v_startInclusive_293_ = lean_ctor_get(v_s_290_, 1);
v_endExclusive_294_ = lean_ctor_get(v_s_290_, 2);
v___x_295_ = lean_nat_add(v_startInclusive_293_, v_pos_291_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_sub(v_endExclusive_294_, v___x_295_);
v___x_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
lean_dec(v___x_305_);
if (v___x_306_ == 0)
{
uint32_t v___x_307_; uint8_t v___y_314_; uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_307_ = lean_string_utf8_get_fast(v_str_292_, v___x_295_);
v___x_319_ = 33;
v___x_320_ = lean_uint32_dec_eq(v___x_307_, v___x_319_);
if (v___x_320_ == 0)
{
uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 35;
v___x_322_ = lean_uint32_dec_eq(v___x_307_, v___x_321_);
if (v___x_322_ == 0)
{
uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 36;
v___x_324_ = lean_uint32_dec_eq(v___x_307_, v___x_323_);
if (v___x_324_ == 0)
{
uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 37;
v___x_326_ = lean_uint32_dec_eq(v___x_307_, v___x_325_);
if (v___x_326_ == 0)
{
uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 38;
v___x_328_ = lean_uint32_dec_eq(v___x_307_, v___x_327_);
if (v___x_328_ == 0)
{
uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 39;
v___x_330_ = lean_uint32_dec_eq(v___x_307_, v___x_329_);
if (v___x_330_ == 0)
{
uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = 42;
v___x_332_ = lean_uint32_dec_eq(v___x_307_, v___x_331_);
if (v___x_332_ == 0)
{
uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = 43;
v___x_334_ = lean_uint32_dec_eq(v___x_307_, v___x_333_);
if (v___x_334_ == 0)
{
uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 45;
v___x_336_ = lean_uint32_dec_eq(v___x_307_, v___x_335_);
if (v___x_336_ == 0)
{
uint32_t v___x_337_; uint8_t v___x_338_; 
v___x_337_ = 46;
v___x_338_ = lean_uint32_dec_eq(v___x_307_, v___x_337_);
if (v___x_338_ == 0)
{
uint32_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = 94;
v___x_340_ = lean_uint32_dec_eq(v___x_307_, v___x_339_);
if (v___x_340_ == 0)
{
uint32_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 95;
v___x_342_ = lean_uint32_dec_eq(v___x_307_, v___x_341_);
if (v___x_342_ == 0)
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 96;
v___x_344_ = lean_uint32_dec_eq(v___x_307_, v___x_343_);
if (v___x_344_ == 0)
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 124;
v___x_346_ = lean_uint32_dec_eq(v___x_307_, v___x_345_);
if (v___x_346_ == 0)
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 126;
v___x_348_ = lean_uint32_dec_eq(v___x_307_, v___x_347_);
if (v___x_348_ == 0)
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 48;
v___x_350_ = lean_uint32_dec_le(v___x_349_, v___x_307_);
if (v___x_350_ == 0)
{
v___y_314_ = v___x_350_;
goto v___jp_313_;
}
else
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 57;
v___x_352_ = lean_uint32_dec_le(v___x_307_, v___x_351_);
v___y_314_ = v___x_352_;
goto v___jp_313_;
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
v___y_303_ = v___x_310_;
goto v___jp_302_;
}
else
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 122;
v___x_312_ = lean_uint32_dec_le(v___x_307_, v___x_311_);
v___y_303_ = v___x_312_;
goto v___jp_302_;
}
}
v___jp_313_:
{
if (v___y_314_ == 0)
{
uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_315_ = 65;
v___x_316_ = lean_uint32_dec_le(v___x_315_, v___x_307_);
if (v___x_316_ == 0)
{
goto v___jp_308_;
}
else
{
uint32_t v___x_317_; uint8_t v___x_318_; 
v___x_317_ = 90;
v___x_318_ = lean_uint32_dec_le(v___x_307_, v___x_317_);
if (v___x_318_ == 0)
{
goto v___jp_308_;
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
}
else
{
lean_dec(v___x_295_);
return v_pos_291_;
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_297_ = lean_string_utf8_next_fast(v_str_292_, v___x_295_);
v___x_298_ = lean_nat_sub(v___x_297_, v___x_295_);
lean_dec(v___x_295_);
v___x_299_ = lean_nat_add(v_pos_291_, v___x_298_);
lean_dec(v___x_298_);
v___x_300_ = lean_nat_dec_lt(v_pos_291_, v___x_299_);
if (v___x_300_ == 0)
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
v___jp_302_:
{
if (v___y_303_ == 0)
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
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object* v_s_353_, lean_object* v_pos_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v_s_353_, v_pos_354_);
lean_dec_ref(v_s_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(uint32_t v___x_356_, lean_object* v___x_357_, lean_object* v_s_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
lean_object* v_startInclusive_361_; lean_object* v_endExclusive_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_startInclusive_361_ = lean_ctor_get(v___x_357_, 1);
v_endExclusive_362_ = lean_ctor_get(v___x_357_, 2);
v___x_363_ = lean_nat_sub(v_endExclusive_362_, v_startInclusive_361_);
v___x_364_ = lean_nat_dec_eq(v_a_359_, v___x_363_);
lean_dec(v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint32_t v___x_366_; lean_object* v___x_367_; 
v___x_365_ = 34;
v___x_366_ = lean_string_utf8_get_fast(v_s_358_, v_a_359_);
v___x_367_ = lean_string_utf8_next_fast(v_s_358_, v_a_359_);
lean_dec(v_a_359_);
switch(lean_obj_tag(v_b_360_))
{
case 0:
{
uint8_t v___x_374_; 
v___x_374_ = lean_uint32_dec_eq(v___x_366_, v___x_365_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(3);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_375_;
goto _start;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_378_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*1, v___x_364_);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_378_;
goto _start;
}
}
case 1:
{
uint8_t v_escaped_380_; lean_object* v_acc_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_426_; 
v_escaped_380_ = lean_ctor_get_uint8(v_b_360_, sizeof(void*)*1);
v_acc_381_ = lean_ctor_get(v_b_360_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_b_360_);
if (v_isSharedCheck_426_ == 0)
{
v___x_383_ = v_b_360_;
v_isShared_384_ = v_isSharedCheck_426_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_acc_381_);
lean_dec(v_b_360_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_426_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (v_escaped_380_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
lean_del_object(v___x_383_);
v___x_400_ = 92;
v___x_401_ = lean_uint32_dec_eq(v___x_366_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; 
v___x_402_ = lean_uint32_dec_eq(v___x_366_, v___x_365_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 9;
v___x_404_ = lean_uint32_dec_eq(v___x_366_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 32;
v___x_406_ = lean_uint32_dec_eq(v___x_366_, v___x_405_);
if (v___x_406_ == 0)
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 33;
v___x_408_ = lean_uint32_dec_eq(v___x_366_, v___x_407_);
if (v___x_408_ == 0)
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 35;
v___x_410_ = lean_uint32_dec_le(v___x_409_, v___x_366_);
if (v___x_410_ == 0)
{
goto v___jp_395_;
}
else
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 91;
v___x_412_ = lean_uint32_dec_le(v___x_366_, v___x_411_);
if (v___x_412_ == 0)
{
goto v___jp_395_;
}
else
{
goto v___jp_391_;
}
}
}
else
{
goto v___jp_391_;
}
}
else
{
goto v___jp_391_;
}
}
else
{
goto v___jp_391_;
}
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_413_, 0, v_acc_381_);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_413_;
goto _start;
}
}
else
{
uint8_t v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_uint32_dec_eq(v___x_356_, v___x_365_);
v___x_416_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_416_, 0, v_acc_381_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_415_);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_416_;
goto _start;
}
}
else
{
uint32_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 9;
v___x_419_ = lean_uint32_dec_eq(v___x_366_, v___x_418_);
if (v___x_419_ == 0)
{
uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 32;
v___x_421_ = lean_uint32_dec_eq(v___x_366_, v___x_420_);
if (v___x_421_ == 0)
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 33;
v___x_423_ = lean_uint32_dec_le(v___x_422_, v___x_366_);
if (v___x_423_ == 0)
{
lean_del_object(v___x_383_);
lean_dec_ref(v_acc_381_);
goto v___jp_371_;
}
else
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 126;
v___x_425_ = lean_uint32_dec_le(v___x_366_, v___x_424_);
if (v___x_425_ == 0)
{
lean_del_object(v___x_383_);
lean_dec_ref(v_acc_381_);
goto v___jp_371_;
}
else
{
goto v___jp_385_;
}
}
}
else
{
goto v___jp_385_;
}
}
else
{
goto v___jp_385_;
}
}
v___jp_385_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_string_push(v_acc_381_, v___x_366_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*1, v___x_364_);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_388_;
goto _start;
}
}
v___jp_391_:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_string_push(v_acc_381_, v___x_366_);
v___x_393_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*1, v_escaped_380_);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_393_;
goto _start;
}
v___jp_395_:
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 93;
v___x_397_ = lean_uint32_dec_le(v___x_396_, v___x_366_);
if (v___x_397_ == 0)
{
lean_dec_ref(v_acc_381_);
goto v___jp_368_;
}
else
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 126;
v___x_399_ = lean_uint32_dec_le(v___x_366_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v_acc_381_);
goto v___jp_368_;
}
else
{
goto v___jp_391_;
}
}
}
}
}
case 2:
{
lean_object* v___x_427_; 
lean_dec_ref(v_b_360_);
v___x_427_ = lean_box(3);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_427_;
goto _start;
}
default: 
{
v_a_359_ = v___x_367_;
goto _start;
}
}
v___jp_368_:
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(3);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_369_;
goto _start;
}
v___jp_371_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_box(3);
v_a_359_ = v___x_367_;
v_b_360_ = v___x_372_;
goto _start;
}
}
else
{
lean_dec(v_a_359_);
return v_b_360_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v_s_432_, lean_object* v_a_433_, lean_object* v_b_434_){
_start:
{
uint32_t v___x_2507__boxed_435_; lean_object* v_res_436_; 
v___x_2507__boxed_435_ = lean_unbox_uint32(v___x_430_);
lean_dec(v___x_430_);
v_res_436_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_2507__boxed_435_, v___x_431_, v_s_432_, v_a_433_, v_b_434_);
lean_dec_ref(v_s_432_);
lean_dec_ref(v___x_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object* v_s_437_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_string_utf8_byte_size(v_s_437_);
v___x_448_ = lean_nat_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
uint32_t v___x_449_; uint32_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = 34;
v___x_450_ = lean_string_utf8_get_fast(v_s_437_, v___x_446_);
v___x_451_ = lean_uint32_dec_eq(v___x_450_, v___x_449_);
if (v___x_451_ == 0)
{
goto v___jp_438_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc_ref(v_s_437_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v_s_437_);
lean_ctor_set(v___x_452_, 1, v___x_446_);
lean_ctor_set(v___x_452_, 2, v___x_447_);
v___x_453_ = lean_box(0);
v___x_454_ = l_String_Slice_positions(v___x_452_);
v___x_455_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_450_, v___x_452_, v_s_437_, v___x_454_, v___x_453_);
lean_dec_ref(v_s_437_);
lean_dec_ref(v___x_452_);
if (lean_obj_tag(v___x_455_) == 2)
{
lean_object* v_result_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_result_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_result_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 1);
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_result_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v___x_455_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
}
else
{
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_string_utf8_byte_size(v_s_437_);
lean_inc_ref(v_s_437_);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_s_437_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
v___x_442_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_441_, v___x_439_);
lean_dec_ref(v___x_441_);
v___x_443_ = lean_nat_dec_eq(v___x_442_, v___x_440_);
lean_dec(v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec_ref(v_s_437_);
v___x_444_ = lean_box(0);
return v___x_444_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_s_437_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(uint32_t v___x_465_, lean_object* v___x_466_, lean_object* v_s_467_, lean_object* v_inst_468_, lean_object* v_R_469_, lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v_c_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_465_, v___x_466_, v_s_467_, v_a_470_, v_b_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v_s_476_, lean_object* v_inst_477_, lean_object* v_R_478_, lean_object* v_a_479_, lean_object* v_b_480_, lean_object* v_c_481_){
_start:
{
uint32_t v___x_2702__boxed_482_; lean_object* v_res_483_; 
v___x_2702__boxed_482_ = lean_unbox_uint32(v___x_474_);
lean_dec(v___x_474_);
v_res_483_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_2702__boxed_482_, v___x_475_, v_s_476_, v_inst_477_, v_R_478_, v_a_479_, v_b_480_, v_c_481_);
lean_dec_ref(v_s_476_);
lean_dec_ref(v___x_475_);
return v_res_483_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
uint8_t v___x_485_; 
v___x_485_ = 1;
return v___x_485_;
}
else
{
lean_object* v_head_486_; lean_object* v_tail_487_; uint8_t v___y_489_; uint8_t v___y_499_; uint32_t v___x_508_; uint32_t v___x_509_; uint8_t v___x_510_; 
v_head_486_ = lean_ctor_get(v_x_484_, 0);
v_tail_487_ = lean_ctor_get(v_x_484_, 1);
v___x_508_ = 33;
v___x_509_ = lean_unbox_uint32(v_head_486_);
v___x_510_ = lean_uint32_dec_eq(v___x_509_, v___x_508_);
if (v___x_510_ == 0)
{
uint32_t v___x_511_; uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = 35;
v___x_512_ = lean_unbox_uint32(v_head_486_);
v___x_513_ = lean_uint32_dec_eq(v___x_512_, v___x_511_);
if (v___x_513_ == 0)
{
uint32_t v___x_514_; uint32_t v___x_515_; uint8_t v___x_516_; 
v___x_514_ = 36;
v___x_515_ = lean_unbox_uint32(v_head_486_);
v___x_516_ = lean_uint32_dec_eq(v___x_515_, v___x_514_);
if (v___x_516_ == 0)
{
uint32_t v___x_517_; uint32_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = 37;
v___x_518_ = lean_unbox_uint32(v_head_486_);
v___x_519_ = lean_uint32_dec_eq(v___x_518_, v___x_517_);
if (v___x_519_ == 0)
{
uint32_t v___x_520_; uint32_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = 38;
v___x_521_ = lean_unbox_uint32(v_head_486_);
v___x_522_ = lean_uint32_dec_eq(v___x_521_, v___x_520_);
if (v___x_522_ == 0)
{
uint32_t v___x_523_; uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = 39;
v___x_524_ = lean_unbox_uint32(v_head_486_);
v___x_525_ = lean_uint32_dec_eq(v___x_524_, v___x_523_);
if (v___x_525_ == 0)
{
uint32_t v___x_526_; uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = 42;
v___x_527_ = lean_unbox_uint32(v_head_486_);
v___x_528_ = lean_uint32_dec_eq(v___x_527_, v___x_526_);
if (v___x_528_ == 0)
{
uint32_t v___x_529_; uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_529_ = 43;
v___x_530_ = lean_unbox_uint32(v_head_486_);
v___x_531_ = lean_uint32_dec_eq(v___x_530_, v___x_529_);
if (v___x_531_ == 0)
{
uint32_t v___x_532_; uint32_t v___x_533_; uint8_t v___x_534_; 
v___x_532_ = 45;
v___x_533_ = lean_unbox_uint32(v_head_486_);
v___x_534_ = lean_uint32_dec_eq(v___x_533_, v___x_532_);
if (v___x_534_ == 0)
{
uint32_t v___x_535_; uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = 46;
v___x_536_ = lean_unbox_uint32(v_head_486_);
v___x_537_ = lean_uint32_dec_eq(v___x_536_, v___x_535_);
if (v___x_537_ == 0)
{
uint32_t v___x_538_; uint32_t v___x_539_; uint8_t v___x_540_; 
v___x_538_ = 94;
v___x_539_ = lean_unbox_uint32(v_head_486_);
v___x_540_ = lean_uint32_dec_eq(v___x_539_, v___x_538_);
if (v___x_540_ == 0)
{
uint32_t v___x_541_; uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_541_ = 95;
v___x_542_ = lean_unbox_uint32(v_head_486_);
v___x_543_ = lean_uint32_dec_eq(v___x_542_, v___x_541_);
if (v___x_543_ == 0)
{
uint32_t v___x_544_; uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_544_ = 96;
v___x_545_ = lean_unbox_uint32(v_head_486_);
v___x_546_ = lean_uint32_dec_eq(v___x_545_, v___x_544_);
if (v___x_546_ == 0)
{
uint32_t v___x_547_; uint32_t v___x_548_; uint8_t v___x_549_; 
v___x_547_ = 124;
v___x_548_ = lean_unbox_uint32(v_head_486_);
v___x_549_ = lean_uint32_dec_eq(v___x_548_, v___x_547_);
if (v___x_549_ == 0)
{
uint32_t v___x_550_; uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_550_ = 126;
v___x_551_ = lean_unbox_uint32(v_head_486_);
v___x_552_ = lean_uint32_dec_eq(v___x_551_, v___x_550_);
if (v___x_552_ == 0)
{
uint32_t v___x_553_; uint32_t v___x_554_; uint8_t v___x_555_; 
v___x_553_ = 48;
v___x_554_ = lean_unbox_uint32(v_head_486_);
v___x_555_ = lean_uint32_dec_le(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
v___y_499_ = v___x_555_;
goto v___jp_498_;
}
else
{
uint32_t v___x_556_; uint32_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = 57;
v___x_557_ = lean_unbox_uint32(v_head_486_);
v___x_558_ = lean_uint32_dec_le(v___x_557_, v___x_556_);
v___y_499_ = v___x_558_;
goto v___jp_498_;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
v___jp_488_:
{
if (v___y_489_ == 0)
{
return v___y_489_;
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
v___jp_491_:
{
uint32_t v___x_492_; uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = 97;
v___x_493_ = lean_unbox_uint32(v_head_486_);
v___x_494_ = lean_uint32_dec_le(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
v___y_489_ = v___x_494_;
goto v___jp_488_;
}
else
{
uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = 122;
v___x_496_ = lean_unbox_uint32(v_head_486_);
v___x_497_ = lean_uint32_dec_le(v___x_496_, v___x_495_);
v___y_489_ = v___x_497_;
goto v___jp_488_;
}
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = 65;
v___x_501_ = lean_unbox_uint32(v_head_486_);
v___x_502_ = lean_uint32_dec_le(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
goto v___jp_491_;
}
else
{
uint32_t v___x_503_; uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = 90;
v___x_504_ = lean_unbox_uint32(v_head_486_);
v___x_505_ = lean_uint32_dec_le(v___x_504_, v___x_503_);
if (v___x_505_ == 0)
{
goto v___jp_491_;
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
}
else
{
v_x_484_ = v_tail_487_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_isToken_spec__0___boxed(lean_object* v_x_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_x_574_);
lean_dec(v_x_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken(lean_object* v_s_577_){
_start:
{
lean_object* v_s_578_; uint8_t v___x_579_; 
v_s_578_ = lean_string_data(v_s_577_);
v___x_579_ = l_List_isEmpty___redArg(v_s_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; 
v___x_580_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_s_578_);
lean_dec(v_s_578_);
return v___x_580_;
}
else
{
uint8_t v___x_581_; 
lean_dec(v_s_578_);
v___x_581_ = 0;
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object* v_s_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Std_Http_Internal_isToken(v_s_582_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal_Char(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_Char(builtin);
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
