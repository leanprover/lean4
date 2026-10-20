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
lean_object* v_head_55_; lean_object* v_tail_56_; uint32_t v___x_73_; uint32_t v___x_74_; uint8_t v___x_75_; 
v_head_55_ = lean_ctor_get(v_x_53_, 0);
v_tail_56_ = lean_ctor_get(v_x_53_, 1);
v___x_73_ = 33;
v___x_74_ = lean_unbox_uint32(v_head_55_);
v___x_75_ = lean_uint32_dec_eq(v___x_74_, v___x_73_);
if (v___x_75_ == 0)
{
uint32_t v___x_76_; uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_76_ = 35;
v___x_77_ = lean_unbox_uint32(v_head_55_);
v___x_78_ = lean_uint32_dec_eq(v___x_77_, v___x_76_);
if (v___x_78_ == 0)
{
uint32_t v___x_79_; uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_79_ = 36;
v___x_80_ = lean_unbox_uint32(v_head_55_);
v___x_81_ = lean_uint32_dec_eq(v___x_80_, v___x_79_);
if (v___x_81_ == 0)
{
uint32_t v___x_82_; uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_82_ = 37;
v___x_83_ = lean_unbox_uint32(v_head_55_);
v___x_84_ = lean_uint32_dec_eq(v___x_83_, v___x_82_);
if (v___x_84_ == 0)
{
uint32_t v___x_85_; uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_85_ = 38;
v___x_86_ = lean_unbox_uint32(v_head_55_);
v___x_87_ = lean_uint32_dec_eq(v___x_86_, v___x_85_);
if (v___x_87_ == 0)
{
uint32_t v___x_88_; uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_88_ = 39;
v___x_89_ = lean_unbox_uint32(v_head_55_);
v___x_90_ = lean_uint32_dec_eq(v___x_89_, v___x_88_);
if (v___x_90_ == 0)
{
uint32_t v___x_91_; uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_91_ = 42;
v___x_92_ = lean_unbox_uint32(v_head_55_);
v___x_93_ = lean_uint32_dec_eq(v___x_92_, v___x_91_);
if (v___x_93_ == 0)
{
uint32_t v___x_94_; uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_94_ = 43;
v___x_95_ = lean_unbox_uint32(v_head_55_);
v___x_96_ = lean_uint32_dec_eq(v___x_95_, v___x_94_);
if (v___x_96_ == 0)
{
uint32_t v___x_97_; uint32_t v___x_98_; uint8_t v___x_99_; 
v___x_97_ = 45;
v___x_98_ = lean_unbox_uint32(v_head_55_);
v___x_99_ = lean_uint32_dec_eq(v___x_98_, v___x_97_);
if (v___x_99_ == 0)
{
uint32_t v___x_100_; uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_100_ = 46;
v___x_101_ = lean_unbox_uint32(v_head_55_);
v___x_102_ = lean_uint32_dec_eq(v___x_101_, v___x_100_);
if (v___x_102_ == 0)
{
uint32_t v___x_103_; uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_103_ = 94;
v___x_104_ = lean_unbox_uint32(v_head_55_);
v___x_105_ = lean_uint32_dec_eq(v___x_104_, v___x_103_);
if (v___x_105_ == 0)
{
uint32_t v___x_106_; uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_106_ = 95;
v___x_107_ = lean_unbox_uint32(v_head_55_);
v___x_108_ = lean_uint32_dec_eq(v___x_107_, v___x_106_);
if (v___x_108_ == 0)
{
uint32_t v___x_109_; uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_109_ = 96;
v___x_110_ = lean_unbox_uint32(v_head_55_);
v___x_111_ = lean_uint32_dec_eq(v___x_110_, v___x_109_);
if (v___x_111_ == 0)
{
uint32_t v___x_112_; uint32_t v___x_113_; uint8_t v___x_114_; 
v___x_112_ = 124;
v___x_113_ = lean_unbox_uint32(v_head_55_);
v___x_114_ = lean_uint32_dec_eq(v___x_113_, v___x_112_);
if (v___x_114_ == 0)
{
uint32_t v___x_115_; uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_115_ = 126;
v___x_116_ = lean_unbox_uint32(v_head_55_);
v___x_117_ = lean_uint32_dec_eq(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
uint32_t v___x_118_; uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_118_ = 48;
v___x_119_ = lean_unbox_uint32(v_head_55_);
v___x_120_ = lean_uint32_dec_le(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
goto v___jp_65_;
}
else
{
uint32_t v___x_121_; uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_121_ = 57;
v___x_122_ = lean_unbox_uint32(v_head_55_);
v___x_123_ = lean_uint32_dec_le(v___x_122_, v___x_121_);
if (v___x_123_ == 0)
{
goto v___jp_65_;
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
uint32_t v___x_58_; uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = 97;
v___x_59_ = lean_unbox_uint32(v_head_55_);
v___x_60_ = lean_uint32_dec_le(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
return v___x_60_;
}
else
{
uint32_t v___x_61_; uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_61_ = 122;
v___x_62_ = lean_unbox_uint32(v_head_55_);
v___x_63_ = lean_uint32_dec_le(v___x_62_, v___x_61_);
if (v___x_63_ == 0)
{
return v___x_63_;
}
else
{
v_x_53_ = v_tail_56_;
goto _start;
}
}
}
v___jp_65_:
{
uint32_t v___x_66_; uint32_t v___x_67_; uint8_t v___x_68_; 
v___x_66_ = 65;
v___x_67_ = lean_unbox_uint32(v_head_55_);
v___x_68_ = lean_uint32_dec_le(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
goto v___jp_57_;
}
else
{
uint32_t v___x_69_; uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_69_ = 90;
v___x_70_ = lean_unbox_uint32(v_head_55_);
v___x_71_ = lean_uint32_dec_le(v___x_70_, v___x_69_);
if (v___x_71_ == 0)
{
goto v___jp_57_;
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
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1___boxed(lean_object* v_x_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_x_140_);
lean_dec(v_x_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object* v_s_144_){
_start:
{
lean_object* v_sl_145_; uint8_t v___x_150_; 
lean_inc_ref(v_s_144_);
v_sl_145_ = l_String_toListImpl(v_s_144_);
v___x_150_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_sl_145_);
if (v___x_150_ == 0)
{
lean_dec_ref(v_s_144_);
goto v___jp_146_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = l_List_isEmpty___redArg(v_sl_145_);
if (v___x_151_ == 0)
{
lean_dec(v_sl_145_);
return v_s_144_;
}
else
{
lean_dec_ref(v_s_144_);
goto v___jp_146_;
}
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString___redArg___closed__0));
v___x_148_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v___x_147_, v_sl_145_);
lean_dec(v_sl_145_);
v___x_149_ = lean_string_append(v___x_148_, v___x_147_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object* v_s_152_, lean_object* v_h_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_152_);
return v___x_154_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
uint8_t v___x_156_; 
v___x_156_ = 1;
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; uint32_t v___x_183_; uint32_t v___x_184_; uint8_t v___x_185_; 
v_head_157_ = lean_ctor_get(v_x_155_, 0);
v_tail_158_ = lean_ctor_get(v_x_155_, 1);
v___x_183_ = 9;
v___x_184_ = lean_unbox_uint32(v_head_157_);
v___x_185_ = lean_uint32_dec_eq(v___x_184_, v___x_183_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint32_t v___x_187_; uint8_t v___x_188_; 
v___x_186_ = 32;
v___x_187_ = lean_unbox_uint32(v_head_157_);
v___x_188_ = lean_uint32_dec_eq(v___x_187_, v___x_186_);
if (v___x_188_ == 0)
{
uint32_t v___x_189_; uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_189_ = 33;
v___x_190_ = lean_unbox_uint32(v_head_157_);
v___x_191_ = lean_uint32_dec_eq(v___x_190_, v___x_189_);
if (v___x_191_ == 0)
{
uint32_t v___x_192_; uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_192_ = 35;
v___x_193_ = lean_unbox_uint32(v_head_157_);
v___x_194_ = lean_uint32_dec_le(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
goto v___jp_175_;
}
else
{
uint32_t v___x_195_; uint32_t v___x_196_; uint8_t v___x_197_; 
v___x_195_ = 91;
v___x_196_ = lean_unbox_uint32(v_head_157_);
v___x_197_ = lean_uint32_dec_le(v___x_196_, v___x_195_);
if (v___x_197_ == 0)
{
goto v___jp_175_;
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
v___jp_159_:
{
uint32_t v___x_160_; uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_160_ = 9;
v___x_161_ = lean_unbox_uint32(v_head_157_);
v___x_162_ = lean_uint32_dec_eq(v___x_161_, v___x_160_);
if (v___x_162_ == 0)
{
uint32_t v___x_163_; uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = 32;
v___x_164_ = lean_unbox_uint32(v_head_157_);
v___x_165_ = lean_uint32_dec_eq(v___x_164_, v___x_163_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = 33;
v___x_167_ = lean_unbox_uint32(v_head_157_);
v___x_168_ = lean_uint32_dec_le(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
uint32_t v___x_169_; uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_169_ = 126;
v___x_170_ = lean_unbox_uint32(v_head_157_);
v___x_171_ = lean_uint32_dec_le(v___x_170_, v___x_169_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
v___jp_175_:
{
uint32_t v___x_176_; uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_176_ = 93;
v___x_177_ = lean_unbox_uint32(v_head_157_);
v___x_178_ = lean_uint32_dec_le(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
goto v___jp_159_;
}
else
{
uint32_t v___x_179_; uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = 126;
v___x_180_ = lean_unbox_uint32(v_head_157_);
v___x_181_ = lean_uint32_dec_le(v___x_180_, v___x_179_);
if (v___x_181_ == 0)
{
goto v___jp_159_;
}
else
{
v_x_155_ = v_tail_158_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(lean_object* v_x_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_202_);
lean_dec(v_x_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object* v_s_205_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
lean_inc_ref(v_s_205_);
v___x_206_ = l_String_toListImpl(v_s_205_);
v___x_207_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v___x_206_);
lean_dec(v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_s_205_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_205_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object* v_msg_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_213_ = lean_panic_fn_borrowed(v___x_212_, v_msg_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__2));
v___x_218_ = lean_unsigned_to_nat(12u);
v___x_219_ = lean_unsigned_to_nat(84u);
v___x_220_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__1));
v___x_221_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__0));
v___x_222_ = l_mkPanicMessageWithDecl(v___x_221_, v___x_220_, v___x_219_, v___x_218_, v___x_217_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object* v_s_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Std_Http_Internal_quoteHttpString_x21___closed__3, &l_Std_Http_Internal_quoteHttpString_x21___closed__3_once, _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3);
v___x_226_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_val_227_; 
v_val_227_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_224_, 1);
return v_val_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(lean_object* v_x_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_tag_nat(v_x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl___boxed(lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(v_x_230_);
lean_dec(v_x_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object* v_t_232_, lean_object* v_k_233_){
_start:
{
switch(lean_obj_tag(v_t_232_))
{
case 1:
{
uint8_t v_escaped_234_; lean_object* v_acc_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_escaped_234_ = lean_ctor_get_uint8(v_t_232_, sizeof(void*)*1);
v_acc_235_ = lean_ctor_get(v_t_232_, 0);
lean_inc_ref(v_acc_235_);
lean_dec_ref_known(v_t_232_, 1);
v___x_236_ = lean_box(v_escaped_234_);
v___x_237_ = lean_apply_2(v_k_233_, v___x_236_, v_acc_235_);
return v___x_237_;
}
case 2:
{
lean_object* v_result_238_; lean_object* v___x_239_; 
v_result_238_ = lean_ctor_get(v_t_232_, 0);
lean_inc_ref(v_result_238_);
lean_dec_ref_known(v_t_232_, 1);
v___x_239_ = lean_apply_1(v_k_233_, v_result_238_);
return v___x_239_;
}
default: 
{
lean_dec(v_t_232_);
return v_k_233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object* v_motive_240_, lean_object* v_ctorIdx_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_k_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_242_, v_k_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object* v_motive_246_, lean_object* v_ctorIdx_247_, lean_object* v_t_248_, lean_object* v_h_249_, lean_object* v_k_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(v_motive_246_, v_ctorIdx_247_, v_t_248_, v_h_249_, v_k_250_);
lean_dec(v_ctorIdx_247_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object* v_t_252_, lean_object* v_start_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_252_, v_start_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object* v_motive_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_start_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_256_, v_start_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object* v_t_260_, lean_object* v_valid_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_260_, v_valid_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_valid_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_264_, v_valid_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object* v_t_268_, lean_object* v_done_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_268_, v_done_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object* v_motive_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_done_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_272_, v_done_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object* v_t_276_, lean_object* v_invalid_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_276_, v_invalid_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_invalid_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_280_, v_invalid_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object* v_s_284_, lean_object* v_pos_285_){
_start:
{
lean_object* v_str_286_; lean_object* v_startInclusive_287_; lean_object* v_endExclusive_288_; lean_object* v___x_289_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v_decide_300_; 
v_str_286_ = lean_ctor_get(v_s_284_, 0);
v_startInclusive_287_ = lean_ctor_get(v_s_284_, 1);
v_endExclusive_288_ = lean_ctor_get(v_s_284_, 2);
v___x_289_ = lean_nat_add(v_startInclusive_287_, v_pos_285_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_sub(v_endExclusive_288_, v___x_289_);
v_decide_300_ = lean_nat_dec_eq(v___x_298_, v___x_299_);
lean_dec(v___x_299_);
if (v_decide_300_ == 0)
{
uint32_t v___x_301_; uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_301_ = lean_string_utf8_get_fast(v_str_286_, v___x_289_);
v___x_312_ = 33;
v___x_313_ = lean_uint32_dec_eq(v___x_301_, v___x_312_);
if (v___x_313_ == 0)
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 35;
v___x_315_ = lean_uint32_dec_eq(v___x_301_, v___x_314_);
if (v___x_315_ == 0)
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 36;
v___x_317_ = lean_uint32_dec_eq(v___x_301_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 37;
v___x_319_ = lean_uint32_dec_eq(v___x_301_, v___x_318_);
if (v___x_319_ == 0)
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 38;
v___x_321_ = lean_uint32_dec_eq(v___x_301_, v___x_320_);
if (v___x_321_ == 0)
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 39;
v___x_323_ = lean_uint32_dec_eq(v___x_301_, v___x_322_);
if (v___x_323_ == 0)
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 42;
v___x_325_ = lean_uint32_dec_eq(v___x_301_, v___x_324_);
if (v___x_325_ == 0)
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 43;
v___x_327_ = lean_uint32_dec_eq(v___x_301_, v___x_326_);
if (v___x_327_ == 0)
{
uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 45;
v___x_329_ = lean_uint32_dec_eq(v___x_301_, v___x_328_);
if (v___x_329_ == 0)
{
uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 46;
v___x_331_ = lean_uint32_dec_eq(v___x_301_, v___x_330_);
if (v___x_331_ == 0)
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 94;
v___x_333_ = lean_uint32_dec_eq(v___x_301_, v___x_332_);
if (v___x_333_ == 0)
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 95;
v___x_335_ = lean_uint32_dec_eq(v___x_301_, v___x_334_);
if (v___x_335_ == 0)
{
uint32_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = 96;
v___x_337_ = lean_uint32_dec_eq(v___x_301_, v___x_336_);
if (v___x_337_ == 0)
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 124;
v___x_339_ = lean_uint32_dec_eq(v___x_301_, v___x_338_);
if (v___x_339_ == 0)
{
uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 126;
v___x_341_ = lean_uint32_dec_eq(v___x_301_, v___x_340_);
if (v___x_341_ == 0)
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 48;
v___x_343_ = lean_uint32_dec_le(v___x_342_, v___x_301_);
if (v___x_343_ == 0)
{
goto v___jp_307_;
}
else
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 57;
v___x_345_ = lean_uint32_dec_le(v___x_301_, v___x_344_);
if (v___x_345_ == 0)
{
goto v___jp_307_;
}
else
{
goto v___jp_290_;
}
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
}
else
{
goto v___jp_290_;
}
v___jp_302_:
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 97;
v___x_304_ = lean_uint32_dec_le(v___x_303_, v___x_301_);
if (v___x_304_ == 0)
{
lean_dec(v___x_289_);
return v_pos_285_;
}
else
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 122;
v___x_306_ = lean_uint32_dec_le(v___x_301_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v___x_289_);
return v_pos_285_;
}
else
{
goto v___jp_290_;
}
}
}
v___jp_307_:
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 65;
v___x_309_ = lean_uint32_dec_le(v___x_308_, v___x_301_);
if (v___x_309_ == 0)
{
goto v___jp_302_;
}
else
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 90;
v___x_311_ = lean_uint32_dec_le(v___x_301_, v___x_310_);
if (v___x_311_ == 0)
{
goto v___jp_302_;
}
else
{
goto v___jp_290_;
}
}
}
}
else
{
lean_dec(v___x_289_);
return v_pos_285_;
}
v___jp_290_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_291_ = lean_string_utf8_next_fast(v_str_286_, v___x_289_);
v___x_292_ = lean_nat_sub(v___x_291_, v___x_289_);
lean_dec(v___x_289_);
v___x_293_ = lean_nat_add(v_pos_285_, v___x_292_);
lean_dec(v___x_292_);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_pos_285_, v___x_294_);
v___x_296_ = lean_nat_dec_le(v___x_295_, v___x_293_);
lean_dec(v___x_295_);
if (v___x_296_ == 0)
{
lean_dec(v___x_293_);
return v_pos_285_;
}
else
{
lean_dec(v_pos_285_);
v_pos_285_ = v___x_293_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object* v_s_346_, lean_object* v_pos_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v_s_346_, v_pos_347_);
lean_dec_ref(v_s_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(lean_object* v___x_349_, lean_object* v___x_350_, uint32_t v___x_351_, lean_object* v___x_352_, lean_object* v_s_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
uint8_t v_decide_356_; 
v_decide_356_ = lean_nat_dec_eq(v_a_354_, v___x_352_);
if (v_decide_356_ == 0)
{
uint32_t v___x_357_; uint8_t v_decide_358_; uint32_t v___x_359_; lean_object* v___x_360_; 
v___x_357_ = 34;
v_decide_358_ = lean_nat_dec_eq(v___x_349_, v___x_350_);
v___x_359_ = lean_string_utf8_get_fast(v_s_353_, v_a_354_);
v___x_360_ = lean_string_utf8_next_fast(v_s_353_, v_a_354_);
lean_dec(v_a_354_);
switch(lean_obj_tag(v_b_355_))
{
case 0:
{
uint8_t v___x_361_; 
v___x_361_ = lean_uint32_dec_eq(v___x_359_, v___x_357_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(3);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_362_;
goto _start;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_365_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v_decide_358_);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_365_;
goto _start;
}
}
case 1:
{
uint8_t v_escaped_367_; lean_object* v_acc_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_421_; 
v_escaped_367_ = lean_ctor_get_uint8(v_b_355_, sizeof(void*)*1);
v_acc_368_ = lean_ctor_get(v_b_355_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_b_355_);
if (v_isSharedCheck_421_ == 0)
{
v___x_370_ = v_b_355_;
v_isShared_371_ = v_isSharedCheck_421_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_acc_368_);
lean_dec(v_b_355_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_421_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
if (v_escaped_367_ == 0)
{
uint32_t v___x_378_; uint8_t v___x_379_; 
lean_del_object(v___x_370_);
v___x_378_ = 92;
v___x_379_ = lean_uint32_dec_eq(v___x_359_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = lean_uint32_dec_eq(v___x_359_, v___x_357_);
if (v___x_380_ == 0)
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 9;
v___x_395_ = lean_uint32_dec_eq(v___x_359_, v___x_394_);
if (v___x_395_ == 0)
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 32;
v___x_397_ = lean_uint32_dec_eq(v___x_359_, v___x_396_);
if (v___x_397_ == 0)
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 33;
v___x_399_ = lean_uint32_dec_eq(v___x_359_, v___x_398_);
if (v___x_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 35;
v___x_401_ = lean_uint32_dec_le(v___x_400_, v___x_359_);
if (v___x_401_ == 0)
{
goto v___jp_385_;
}
else
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 91;
v___x_403_ = lean_uint32_dec_le(v___x_359_, v___x_402_);
if (v___x_403_ == 0)
{
goto v___jp_385_;
}
else
{
goto v___jp_381_;
}
}
}
else
{
goto v___jp_381_;
}
}
else
{
goto v___jp_381_;
}
}
else
{
goto v___jp_381_;
}
}
else
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_404_, 0, v_acc_368_);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_404_;
goto _start;
}
v___jp_381_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_string_push(v_acc_368_, v___x_359_);
v___x_383_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*1, v___x_380_);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_383_;
goto _start;
}
v___jp_385_:
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 93;
v___x_387_ = lean_uint32_dec_le(v___x_386_, v___x_359_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v_acc_368_);
v___x_388_ = lean_box(3);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_388_;
goto _start;
}
else
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 126;
v___x_391_ = lean_uint32_dec_le(v___x_359_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v_acc_368_);
v___x_392_ = lean_box(3);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_392_;
goto _start;
}
else
{
goto v___jp_381_;
}
}
}
}
else
{
uint8_t v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_uint32_dec_eq(v___x_351_, v___x_357_);
v___x_407_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_407_, 0, v_acc_368_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*1, v___x_406_);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_407_;
goto _start;
}
}
else
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 9;
v___x_410_ = lean_uint32_dec_eq(v___x_359_, v___x_409_);
if (v___x_410_ == 0)
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 32;
v___x_412_ = lean_uint32_dec_eq(v___x_359_, v___x_411_);
if (v___x_412_ == 0)
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 33;
v___x_414_ = lean_uint32_dec_le(v___x_413_, v___x_359_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_del_object(v___x_370_);
lean_dec_ref(v_acc_368_);
v___x_415_ = lean_box(3);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_415_;
goto _start;
}
else
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 126;
v___x_418_ = lean_uint32_dec_le(v___x_359_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_del_object(v___x_370_);
lean_dec_ref(v_acc_368_);
v___x_419_ = lean_box(3);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_419_;
goto _start;
}
else
{
goto v___jp_372_;
}
}
}
else
{
goto v___jp_372_;
}
}
else
{
goto v___jp_372_;
}
}
v___jp_372_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_string_push(v_acc_368_, v___x_359_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_373_);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v_decide_358_);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_375_;
goto _start;
}
}
}
}
case 2:
{
lean_object* v___x_422_; 
lean_dec_ref_known(v_b_355_, 1);
v___x_422_ = lean_box(3);
v_a_354_ = v___x_360_;
v_b_355_ = v___x_422_;
goto _start;
}
default: 
{
v_a_354_ = v___x_360_;
goto _start;
}
}
}
else
{
lean_dec(v_a_354_);
return v_b_355_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v_s_429_, lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
uint32_t v___x_2559__boxed_432_; lean_object* v_res_433_; 
v___x_2559__boxed_432_ = lean_unbox_uint32(v___x_427_);
lean_dec(v___x_427_);
v_res_433_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_425_, v___x_426_, v___x_2559__boxed_432_, v___x_428_, v_s_429_, v_a_430_, v_b_431_);
lean_dec_ref(v_s_429_);
lean_dec(v___x_428_);
lean_dec(v___x_426_);
lean_dec(v___x_425_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object* v_s_434_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v_decide_445_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_string_utf8_byte_size(v_s_434_);
v_decide_445_ = lean_nat_dec_eq(v___x_443_, v___x_444_);
if (v_decide_445_ == 0)
{
uint32_t v___x_446_; uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_446_ = 34;
v___x_447_ = lean_string_utf8_get_fast(v_s_434_, v___x_443_);
v___x_448_ = lean_uint32_dec_eq(v___x_447_, v___x_446_);
if (v___x_448_ == 0)
{
goto v___jp_435_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_box(0);
v___x_450_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_443_, v___x_444_, v___x_447_, v___x_444_, v_s_434_, v___x_443_, v___x_449_);
lean_dec_ref(v_s_434_);
if (lean_obj_tag(v___x_450_) == 2)
{
lean_object* v_result_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_result_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_result_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 1);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_result_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v___x_450_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
}
}
else
{
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v_decide_440_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_string_utf8_byte_size(v_s_434_);
lean_inc_ref(v_s_434_);
v___x_438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_438_, 0, v_s_434_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
lean_ctor_set(v___x_438_, 2, v___x_437_);
v___x_439_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_438_, v___x_436_);
lean_dec_ref_known(v___x_438_, 3);
v_decide_440_ = lean_nat_dec_eq(v___x_439_, v___x_437_);
lean_dec(v___x_439_);
if (v_decide_440_ == 0)
{
lean_object* v___x_441_; 
lean_dec_ref(v_s_434_);
v___x_441_ = lean_box(0);
return v___x_441_;
}
else
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_s_434_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, uint32_t v___x_463_, lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v_s_466_, lean_object* v_inst_467_, lean_object* v_R_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_c_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_461_, v___x_462_, v___x_463_, v___x_465_, v_s_466_, v_a_469_, v_b_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v_s_479_, lean_object* v_inst_480_, lean_object* v_R_481_, lean_object* v_a_482_, lean_object* v_b_483_, lean_object* v_c_484_){
_start:
{
uint32_t v___x_2761__boxed_485_; lean_object* v_res_486_; 
v___x_2761__boxed_485_ = lean_unbox_uint32(v___x_476_);
lean_dec(v___x_476_);
v_res_486_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_473_, v___x_474_, v___x_475_, v___x_2761__boxed_485_, v___x_477_, v___x_478_, v_s_479_, v_inst_480_, v_R_481_, v_a_482_, v_b_483_, v_c_484_);
lean_dec_ref(v_s_479_);
lean_dec(v___x_478_);
lean_dec_ref(v___x_477_);
lean_dec(v___x_475_);
lean_dec(v___x_474_);
lean_dec_ref(v___x_473_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
uint8_t v___x_488_; 
v___x_488_ = 1;
return v___x_488_;
}
else
{
lean_object* v_head_489_; lean_object* v_tail_490_; uint32_t v___x_507_; uint32_t v___x_508_; uint8_t v___x_509_; 
v_head_489_ = lean_ctor_get(v_x_487_, 0);
v_tail_490_ = lean_ctor_get(v_x_487_, 1);
v___x_507_ = 33;
v___x_508_ = lean_unbox_uint32(v_head_489_);
v___x_509_ = lean_uint32_dec_eq(v___x_508_, v___x_507_);
if (v___x_509_ == 0)
{
uint32_t v___x_510_; uint32_t v___x_511_; uint8_t v___x_512_; 
v___x_510_ = 35;
v___x_511_ = lean_unbox_uint32(v_head_489_);
v___x_512_ = lean_uint32_dec_eq(v___x_511_, v___x_510_);
if (v___x_512_ == 0)
{
uint32_t v___x_513_; uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = 36;
v___x_514_ = lean_unbox_uint32(v_head_489_);
v___x_515_ = lean_uint32_dec_eq(v___x_514_, v___x_513_);
if (v___x_515_ == 0)
{
uint32_t v___x_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_516_ = 37;
v___x_517_ = lean_unbox_uint32(v_head_489_);
v___x_518_ = lean_uint32_dec_eq(v___x_517_, v___x_516_);
if (v___x_518_ == 0)
{
uint32_t v___x_519_; uint32_t v___x_520_; uint8_t v___x_521_; 
v___x_519_ = 38;
v___x_520_ = lean_unbox_uint32(v_head_489_);
v___x_521_ = lean_uint32_dec_eq(v___x_520_, v___x_519_);
if (v___x_521_ == 0)
{
uint32_t v___x_522_; uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = 39;
v___x_523_ = lean_unbox_uint32(v_head_489_);
v___x_524_ = lean_uint32_dec_eq(v___x_523_, v___x_522_);
if (v___x_524_ == 0)
{
uint32_t v___x_525_; uint32_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = 42;
v___x_526_ = lean_unbox_uint32(v_head_489_);
v___x_527_ = lean_uint32_dec_eq(v___x_526_, v___x_525_);
if (v___x_527_ == 0)
{
uint32_t v___x_528_; uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_528_ = 43;
v___x_529_ = lean_unbox_uint32(v_head_489_);
v___x_530_ = lean_uint32_dec_eq(v___x_529_, v___x_528_);
if (v___x_530_ == 0)
{
uint32_t v___x_531_; uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_531_ = 45;
v___x_532_ = lean_unbox_uint32(v_head_489_);
v___x_533_ = lean_uint32_dec_eq(v___x_532_, v___x_531_);
if (v___x_533_ == 0)
{
uint32_t v___x_534_; uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_534_ = 46;
v___x_535_ = lean_unbox_uint32(v_head_489_);
v___x_536_ = lean_uint32_dec_eq(v___x_535_, v___x_534_);
if (v___x_536_ == 0)
{
uint32_t v___x_537_; uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_537_ = 94;
v___x_538_ = lean_unbox_uint32(v_head_489_);
v___x_539_ = lean_uint32_dec_eq(v___x_538_, v___x_537_);
if (v___x_539_ == 0)
{
uint32_t v___x_540_; uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = 95;
v___x_541_ = lean_unbox_uint32(v_head_489_);
v___x_542_ = lean_uint32_dec_eq(v___x_541_, v___x_540_);
if (v___x_542_ == 0)
{
uint32_t v___x_543_; uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_543_ = 96;
v___x_544_ = lean_unbox_uint32(v_head_489_);
v___x_545_ = lean_uint32_dec_eq(v___x_544_, v___x_543_);
if (v___x_545_ == 0)
{
uint32_t v___x_546_; uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_546_ = 124;
v___x_547_ = lean_unbox_uint32(v_head_489_);
v___x_548_ = lean_uint32_dec_eq(v___x_547_, v___x_546_);
if (v___x_548_ == 0)
{
uint32_t v___x_549_; uint32_t v___x_550_; uint8_t v___x_551_; 
v___x_549_ = 126;
v___x_550_ = lean_unbox_uint32(v_head_489_);
v___x_551_ = lean_uint32_dec_eq(v___x_550_, v___x_549_);
if (v___x_551_ == 0)
{
uint32_t v___x_552_; uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = 48;
v___x_553_ = lean_unbox_uint32(v_head_489_);
v___x_554_ = lean_uint32_dec_le(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
goto v___jp_499_;
}
else
{
uint32_t v___x_555_; uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 57;
v___x_556_ = lean_unbox_uint32(v_head_489_);
v___x_557_ = lean_uint32_dec_le(v___x_556_, v___x_555_);
if (v___x_557_ == 0)
{
goto v___jp_499_;
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
v___jp_491_:
{
uint32_t v___x_492_; uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = 97;
v___x_493_ = lean_unbox_uint32(v_head_489_);
v___x_494_ = lean_uint32_dec_le(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
return v___x_494_;
}
else
{
uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = 122;
v___x_496_ = lean_unbox_uint32(v_head_489_);
v___x_497_ = lean_uint32_dec_le(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
return v___x_497_;
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
}
}
v___jp_499_:
{
uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = 65;
v___x_501_ = lean_unbox_uint32(v_head_489_);
v___x_502_ = lean_uint32_dec_le(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
goto v___jp_491_;
}
else
{
uint32_t v___x_503_; uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = 90;
v___x_504_ = lean_unbox_uint32(v_head_489_);
v___x_505_ = lean_uint32_dec_le(v___x_504_, v___x_503_);
if (v___x_505_ == 0)
{
goto v___jp_491_;
}
else
{
v_x_487_ = v_tail_490_;
goto _start;
}
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
v_s_578_ = l_String_toListImpl(v_s_577_);
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
