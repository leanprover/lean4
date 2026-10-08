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
lean_object* v_sl_145_; uint8_t v___y_151_; uint8_t v___x_152_; 
lean_inc_ref(v_s_144_);
v_sl_145_ = l_String_toListImpl(v_s_144_);
v___x_152_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_sl_145_);
if (v___x_152_ == 0)
{
v___y_151_ = v___x_152_;
goto v___jp_150_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = l_List_isEmpty___redArg(v_sl_145_);
if (v___x_153_ == 0)
{
v___y_151_ = v___x_152_;
goto v___jp_150_;
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
v___jp_150_:
{
if (v___y_151_ == 0)
{
lean_dec_ref(v_s_144_);
goto v___jp_146_;
}
else
{
lean_dec(v_sl_145_);
return v_s_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object* v_s_154_, lean_object* v_h_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_154_);
return v___x_156_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 1;
return v___x_158_;
}
else
{
lean_object* v_head_159_; lean_object* v_tail_160_; uint32_t v___x_185_; uint32_t v___x_186_; uint8_t v___x_187_; 
v_head_159_ = lean_ctor_get(v_x_157_, 0);
v_tail_160_ = lean_ctor_get(v_x_157_, 1);
v___x_185_ = 9;
v___x_186_ = lean_unbox_uint32(v_head_159_);
v___x_187_ = lean_uint32_dec_eq(v___x_186_, v___x_185_);
if (v___x_187_ == 0)
{
uint32_t v___x_188_; uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_188_ = 32;
v___x_189_ = lean_unbox_uint32(v_head_159_);
v___x_190_ = lean_uint32_dec_eq(v___x_189_, v___x_188_);
if (v___x_190_ == 0)
{
uint32_t v___x_191_; uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_191_ = 33;
v___x_192_ = lean_unbox_uint32(v_head_159_);
v___x_193_ = lean_uint32_dec_eq(v___x_192_, v___x_191_);
if (v___x_193_ == 0)
{
uint32_t v___x_194_; uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = 35;
v___x_195_ = lean_unbox_uint32(v_head_159_);
v___x_196_ = lean_uint32_dec_le(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
goto v___jp_177_;
}
else
{
uint32_t v___x_197_; uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_197_ = 91;
v___x_198_ = lean_unbox_uint32(v_head_159_);
v___x_199_ = lean_uint32_dec_le(v___x_198_, v___x_197_);
if (v___x_199_ == 0)
{
goto v___jp_177_;
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
v___jp_161_:
{
uint32_t v___x_162_; uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_162_ = 9;
v___x_163_ = lean_unbox_uint32(v_head_159_);
v___x_164_ = lean_uint32_dec_eq(v___x_163_, v___x_162_);
if (v___x_164_ == 0)
{
uint32_t v___x_165_; uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_165_ = 32;
v___x_166_ = lean_unbox_uint32(v_head_159_);
v___x_167_ = lean_uint32_dec_eq(v___x_166_, v___x_165_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = 33;
v___x_169_ = lean_unbox_uint32(v_head_159_);
v___x_170_ = lean_uint32_dec_le(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
uint32_t v___x_171_; uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_171_ = 126;
v___x_172_ = lean_unbox_uint32(v_head_159_);
v___x_173_ = lean_uint32_dec_le(v___x_172_, v___x_171_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
v___jp_177_:
{
uint32_t v___x_178_; uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_178_ = 93;
v___x_179_ = lean_unbox_uint32(v_head_159_);
v___x_180_ = lean_uint32_dec_le(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
goto v___jp_161_;
}
else
{
uint32_t v___x_181_; uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = 126;
v___x_182_ = lean_unbox_uint32(v_head_159_);
v___x_183_ = lean_uint32_dec_le(v___x_182_, v___x_181_);
if (v___x_183_ == 0)
{
goto v___jp_161_;
}
else
{
v_x_157_ = v_tail_160_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_204_);
lean_dec(v_x_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object* v_s_207_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
lean_inc_ref(v_s_207_);
v___x_208_ = l_String_toListImpl(v_s_207_);
v___x_209_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v___x_208_);
lean_dec(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v_s_207_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_207_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object* v_msg_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_215_ = lean_panic_fn_borrowed(v___x_214_, v_msg_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__2));
v___x_220_ = lean_unsigned_to_nat(12u);
v___x_221_ = lean_unsigned_to_nat(84u);
v___x_222_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__1));
v___x_223_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__0));
v___x_224_ = l_mkPanicMessageWithDecl(v___x_223_, v___x_222_, v___x_221_, v___x_220_, v___x_219_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object* v_s_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Std_Http_Internal_quoteHttpString_x21___closed__3, &l_Std_Http_Internal_quoteHttpString_x21___closed__3_once, _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3);
v___x_228_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_227_);
return v___x_228_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_226_, 1);
return v_val_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_tag_nat(v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl___boxed(lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___impl(v_x_232_);
lean_dec(v_x_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object* v_t_234_, lean_object* v_k_235_){
_start:
{
switch(lean_obj_tag(v_t_234_))
{
case 1:
{
uint8_t v_escaped_236_; lean_object* v_acc_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_escaped_236_ = lean_ctor_get_uint8(v_t_234_, sizeof(void*)*1);
v_acc_237_ = lean_ctor_get(v_t_234_, 0);
lean_inc_ref(v_acc_237_);
lean_dec_ref_known(v_t_234_, 1);
v___x_238_ = lean_box(v_escaped_236_);
v___x_239_ = lean_apply_2(v_k_235_, v___x_238_, v_acc_237_);
return v___x_239_;
}
case 2:
{
lean_object* v_result_240_; lean_object* v___x_241_; 
v_result_240_ = lean_ctor_get(v_t_234_, 0);
lean_inc_ref(v_result_240_);
lean_dec_ref_known(v_t_234_, 1);
v___x_241_ = lean_apply_1(v_k_235_, v_result_240_);
return v___x_241_;
}
default: 
{
lean_dec(v_t_234_);
return v_k_235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object* v_motive_242_, lean_object* v_ctorIdx_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_k_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_244_, v_k_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(v_motive_248_, v_ctorIdx_249_, v_t_250_, v_h_251_, v_k_252_);
lean_dec(v_ctorIdx_249_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object* v_t_254_, lean_object* v_start_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_254_, v_start_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object* v_motive_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_start_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_258_, v_start_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object* v_t_262_, lean_object* v_valid_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_262_, v_valid_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_valid_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_266_, v_valid_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object* v_t_270_, lean_object* v_done_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_270_, v_done_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_done_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_274_, v_done_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object* v_t_278_, lean_object* v_invalid_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_278_, v_invalid_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_invalid_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_282_, v_invalid_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object* v_s_286_, lean_object* v_pos_287_){
_start:
{
lean_object* v_str_288_; lean_object* v_startInclusive_289_; lean_object* v_endExclusive_290_; lean_object* v___x_291_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v_decide_302_; 
v_str_288_ = lean_ctor_get(v_s_286_, 0);
v_startInclusive_289_ = lean_ctor_get(v_s_286_, 1);
v_endExclusive_290_ = lean_ctor_get(v_s_286_, 2);
v___x_291_ = lean_nat_add(v_startInclusive_289_, v_pos_287_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_sub(v_endExclusive_290_, v___x_291_);
v_decide_302_ = lean_nat_dec_eq(v___x_300_, v___x_301_);
lean_dec(v___x_301_);
if (v_decide_302_ == 0)
{
uint32_t v___x_303_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_303_ = lean_string_utf8_get_fast(v_str_288_, v___x_291_);
v___x_314_ = 33;
v___x_315_ = lean_uint32_dec_eq(v___x_303_, v___x_314_);
if (v___x_315_ == 0)
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 35;
v___x_317_ = lean_uint32_dec_eq(v___x_303_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; uint8_t v___x_319_; 
v___x_318_ = 36;
v___x_319_ = lean_uint32_dec_eq(v___x_303_, v___x_318_);
if (v___x_319_ == 0)
{
uint32_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = 37;
v___x_321_ = lean_uint32_dec_eq(v___x_303_, v___x_320_);
if (v___x_321_ == 0)
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 38;
v___x_323_ = lean_uint32_dec_eq(v___x_303_, v___x_322_);
if (v___x_323_ == 0)
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 39;
v___x_325_ = lean_uint32_dec_eq(v___x_303_, v___x_324_);
if (v___x_325_ == 0)
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 42;
v___x_327_ = lean_uint32_dec_eq(v___x_303_, v___x_326_);
if (v___x_327_ == 0)
{
uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_328_ = 43;
v___x_329_ = lean_uint32_dec_eq(v___x_303_, v___x_328_);
if (v___x_329_ == 0)
{
uint32_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = 45;
v___x_331_ = lean_uint32_dec_eq(v___x_303_, v___x_330_);
if (v___x_331_ == 0)
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 46;
v___x_333_ = lean_uint32_dec_eq(v___x_303_, v___x_332_);
if (v___x_333_ == 0)
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 94;
v___x_335_ = lean_uint32_dec_eq(v___x_303_, v___x_334_);
if (v___x_335_ == 0)
{
uint32_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = 95;
v___x_337_ = lean_uint32_dec_eq(v___x_303_, v___x_336_);
if (v___x_337_ == 0)
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 96;
v___x_339_ = lean_uint32_dec_eq(v___x_303_, v___x_338_);
if (v___x_339_ == 0)
{
uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 124;
v___x_341_ = lean_uint32_dec_eq(v___x_303_, v___x_340_);
if (v___x_341_ == 0)
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 126;
v___x_343_ = lean_uint32_dec_eq(v___x_303_, v___x_342_);
if (v___x_343_ == 0)
{
uint32_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 48;
v___x_345_ = lean_uint32_dec_le(v___x_344_, v___x_303_);
if (v___x_345_ == 0)
{
goto v___jp_309_;
}
else
{
uint32_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = 57;
v___x_347_ = lean_uint32_dec_le(v___x_303_, v___x_346_);
if (v___x_347_ == 0)
{
goto v___jp_309_;
}
else
{
goto v___jp_292_;
}
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
}
else
{
goto v___jp_292_;
}
v___jp_304_:
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 97;
v___x_306_ = lean_uint32_dec_le(v___x_305_, v___x_303_);
if (v___x_306_ == 0)
{
lean_dec(v___x_291_);
return v_pos_287_;
}
else
{
uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = 122;
v___x_308_ = lean_uint32_dec_le(v___x_303_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v___x_291_);
return v_pos_287_;
}
else
{
goto v___jp_292_;
}
}
}
v___jp_309_:
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 65;
v___x_311_ = lean_uint32_dec_le(v___x_310_, v___x_303_);
if (v___x_311_ == 0)
{
goto v___jp_304_;
}
else
{
uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 90;
v___x_313_ = lean_uint32_dec_le(v___x_303_, v___x_312_);
if (v___x_313_ == 0)
{
goto v___jp_304_;
}
else
{
goto v___jp_292_;
}
}
}
}
else
{
lean_dec(v___x_291_);
return v_pos_287_;
}
v___jp_292_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_293_ = lean_string_utf8_next_fast(v_str_288_, v___x_291_);
v___x_294_ = lean_nat_sub(v___x_293_, v___x_291_);
lean_dec(v___x_291_);
v___x_295_ = lean_nat_add(v_pos_287_, v___x_294_);
lean_dec(v___x_294_);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_pos_287_, v___x_296_);
v___x_298_ = lean_nat_dec_le(v___x_297_, v___x_295_);
lean_dec(v___x_297_);
if (v___x_298_ == 0)
{
lean_dec(v___x_295_);
return v_pos_287_;
}
else
{
lean_dec(v_pos_287_);
v_pos_287_ = v___x_295_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object* v_s_348_, lean_object* v_pos_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v_s_348_, v_pos_349_);
lean_dec_ref(v_s_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(lean_object* v___x_351_, lean_object* v___x_352_, uint32_t v___x_353_, lean_object* v___x_354_, lean_object* v_s_355_, lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
uint8_t v_decide_358_; 
v_decide_358_ = lean_nat_dec_eq(v_a_356_, v___x_354_);
if (v_decide_358_ == 0)
{
uint32_t v___x_359_; uint8_t v_decide_360_; uint32_t v___x_361_; lean_object* v___x_362_; 
v___x_359_ = 34;
v_decide_360_ = lean_nat_dec_eq(v___x_351_, v___x_352_);
v___x_361_ = lean_string_utf8_get_fast(v_s_355_, v_a_356_);
v___x_362_ = lean_string_utf8_next_fast(v_s_355_, v_a_356_);
lean_dec(v_a_356_);
switch(lean_obj_tag(v_b_357_))
{
case 0:
{
uint8_t v___x_363_; 
v___x_363_ = lean_uint32_dec_eq(v___x_361_, v___x_359_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(3);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_367_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v_decide_360_);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_367_;
goto _start;
}
}
case 1:
{
uint8_t v_escaped_369_; lean_object* v_acc_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_423_; 
v_escaped_369_ = lean_ctor_get_uint8(v_b_357_, sizeof(void*)*1);
v_acc_370_ = lean_ctor_get(v_b_357_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_b_357_);
if (v_isSharedCheck_423_ == 0)
{
v___x_372_ = v_b_357_;
v_isShared_373_ = v_isSharedCheck_423_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_acc_370_);
lean_dec(v_b_357_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_423_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
if (v_escaped_369_ == 0)
{
uint32_t v___x_380_; uint8_t v___x_381_; 
lean_del_object(v___x_372_);
v___x_380_ = 92;
v___x_381_ = lean_uint32_dec_eq(v___x_361_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = lean_uint32_dec_eq(v___x_361_, v___x_359_);
if (v___x_382_ == 0)
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 9;
v___x_397_ = lean_uint32_dec_eq(v___x_361_, v___x_396_);
if (v___x_397_ == 0)
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 32;
v___x_399_ = lean_uint32_dec_eq(v___x_361_, v___x_398_);
if (v___x_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 33;
v___x_401_ = lean_uint32_dec_eq(v___x_361_, v___x_400_);
if (v___x_401_ == 0)
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 35;
v___x_403_ = lean_uint32_dec_le(v___x_402_, v___x_361_);
if (v___x_403_ == 0)
{
goto v___jp_387_;
}
else
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 91;
v___x_405_ = lean_uint32_dec_le(v___x_361_, v___x_404_);
if (v___x_405_ == 0)
{
goto v___jp_387_;
}
else
{
goto v___jp_383_;
}
}
}
else
{
goto v___jp_383_;
}
}
else
{
goto v___jp_383_;
}
}
else
{
goto v___jp_383_;
}
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_406_, 0, v_acc_370_);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_406_;
goto _start;
}
v___jp_383_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_string_push(v_acc_370_, v___x_361_);
v___x_385_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*1, v___x_382_);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_385_;
goto _start;
}
v___jp_387_:
{
uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = 93;
v___x_389_ = lean_uint32_dec_le(v___x_388_, v___x_361_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v_acc_370_);
v___x_390_ = lean_box(3);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_390_;
goto _start;
}
else
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 126;
v___x_393_ = lean_uint32_dec_le(v___x_361_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v_acc_370_);
v___x_394_ = lean_box(3);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_394_;
goto _start;
}
else
{
goto v___jp_383_;
}
}
}
}
else
{
uint8_t v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_uint32_dec_eq(v___x_353_, v___x_359_);
v___x_409_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_409_, 0, v_acc_370_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_408_);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_409_;
goto _start;
}
}
else
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 9;
v___x_412_ = lean_uint32_dec_eq(v___x_361_, v___x_411_);
if (v___x_412_ == 0)
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 32;
v___x_414_ = lean_uint32_dec_eq(v___x_361_, v___x_413_);
if (v___x_414_ == 0)
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 33;
v___x_416_ = lean_uint32_dec_le(v___x_415_, v___x_361_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_del_object(v___x_372_);
lean_dec_ref(v_acc_370_);
v___x_417_ = lean_box(3);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_417_;
goto _start;
}
else
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 126;
v___x_420_ = lean_uint32_dec_le(v___x_361_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_del_object(v___x_372_);
lean_dec_ref(v_acc_370_);
v___x_421_ = lean_box(3);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_421_;
goto _start;
}
else
{
goto v___jp_374_;
}
}
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
}
v___jp_374_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_string_push(v_acc_370_, v___x_361_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v_decide_360_);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_377_;
goto _start;
}
}
}
}
case 2:
{
lean_object* v___x_424_; 
lean_dec_ref_known(v_b_357_, 1);
v___x_424_ = lean_box(3);
v_a_356_ = v___x_362_;
v_b_357_ = v___x_424_;
goto _start;
}
default: 
{
v_a_356_ = v___x_362_;
goto _start;
}
}
}
else
{
lean_dec(v_a_356_);
return v_b_357_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_s_431_, lean_object* v_a_432_, lean_object* v_b_433_){
_start:
{
uint32_t v___x_2559__boxed_434_; lean_object* v_res_435_; 
v___x_2559__boxed_434_ = lean_unbox_uint32(v___x_429_);
lean_dec(v___x_429_);
v_res_435_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_427_, v___x_428_, v___x_2559__boxed_434_, v___x_430_, v_s_431_, v_a_432_, v_b_433_);
lean_dec_ref(v_s_431_);
lean_dec(v___x_430_);
lean_dec(v___x_428_);
lean_dec(v___x_427_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object* v_s_436_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v_decide_447_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_string_utf8_byte_size(v_s_436_);
v_decide_447_ = lean_nat_dec_eq(v___x_445_, v___x_446_);
if (v_decide_447_ == 0)
{
uint32_t v___x_448_; uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_448_ = 34;
v___x_449_ = lean_string_utf8_get_fast(v_s_436_, v___x_445_);
v___x_450_ = lean_uint32_dec_eq(v___x_449_, v___x_448_);
if (v___x_450_ == 0)
{
goto v___jp_437_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_box(0);
v___x_452_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_445_, v___x_446_, v___x_449_, v___x_446_, v_s_436_, v___x_445_, v___x_451_);
lean_dec_ref(v_s_436_);
if (lean_obj_tag(v___x_452_) == 2)
{
lean_object* v_result_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_result_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_result_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 1);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_result_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v___x_461_; 
lean_dec(v___x_452_);
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
}
else
{
goto v___jp_437_;
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v_decide_442_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_string_utf8_byte_size(v_s_436_);
lean_inc_ref(v_s_436_);
v___x_440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_440_, 0, v_s_436_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
v___x_441_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_440_, v___x_438_);
lean_dec_ref_known(v___x_440_, 3);
v_decide_442_ = lean_nat_dec_eq(v___x_441_, v___x_439_);
lean_dec(v___x_441_);
if (v_decide_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec_ref(v_s_436_);
v___x_443_ = lean_box(0);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_s_436_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v___x_464_, uint32_t v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_s_468_, lean_object* v_inst_469_, lean_object* v_R_470_, lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v_c_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_463_, v___x_464_, v___x_465_, v___x_467_, v_s_468_, v_a_471_, v_b_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v_s_481_, lean_object* v_inst_482_, lean_object* v_R_483_, lean_object* v_a_484_, lean_object* v_b_485_, lean_object* v_c_486_){
_start:
{
uint32_t v___x_2761__boxed_487_; lean_object* v_res_488_; 
v___x_2761__boxed_487_ = lean_unbox_uint32(v___x_478_);
lean_dec(v___x_478_);
v_res_488_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_475_, v___x_476_, v___x_477_, v___x_2761__boxed_487_, v___x_479_, v___x_480_, v_s_481_, v_inst_482_, v_R_483_, v_a_484_, v_b_485_, v_c_486_);
lean_dec_ref(v_s_481_);
lean_dec(v___x_480_);
lean_dec_ref(v___x_479_);
lean_dec(v___x_477_);
lean_dec(v___x_476_);
lean_dec_ref(v___x_475_);
return v_res_488_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
uint8_t v___x_490_; 
v___x_490_ = 1;
return v___x_490_;
}
else
{
lean_object* v_head_491_; lean_object* v_tail_492_; uint32_t v___x_509_; uint32_t v___x_510_; uint8_t v___x_511_; 
v_head_491_ = lean_ctor_get(v_x_489_, 0);
v_tail_492_ = lean_ctor_get(v_x_489_, 1);
v___x_509_ = 33;
v___x_510_ = lean_unbox_uint32(v_head_491_);
v___x_511_ = lean_uint32_dec_eq(v___x_510_, v___x_509_);
if (v___x_511_ == 0)
{
uint32_t v___x_512_; uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_512_ = 35;
v___x_513_ = lean_unbox_uint32(v_head_491_);
v___x_514_ = lean_uint32_dec_eq(v___x_513_, v___x_512_);
if (v___x_514_ == 0)
{
uint32_t v___x_515_; uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_515_ = 36;
v___x_516_ = lean_unbox_uint32(v_head_491_);
v___x_517_ = lean_uint32_dec_eq(v___x_516_, v___x_515_);
if (v___x_517_ == 0)
{
uint32_t v___x_518_; uint32_t v___x_519_; uint8_t v___x_520_; 
v___x_518_ = 37;
v___x_519_ = lean_unbox_uint32(v_head_491_);
v___x_520_ = lean_uint32_dec_eq(v___x_519_, v___x_518_);
if (v___x_520_ == 0)
{
uint32_t v___x_521_; uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_521_ = 38;
v___x_522_ = lean_unbox_uint32(v_head_491_);
v___x_523_ = lean_uint32_dec_eq(v___x_522_, v___x_521_);
if (v___x_523_ == 0)
{
uint32_t v___x_524_; uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = 39;
v___x_525_ = lean_unbox_uint32(v_head_491_);
v___x_526_ = lean_uint32_dec_eq(v___x_525_, v___x_524_);
if (v___x_526_ == 0)
{
uint32_t v___x_527_; uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = 42;
v___x_528_ = lean_unbox_uint32(v_head_491_);
v___x_529_ = lean_uint32_dec_eq(v___x_528_, v___x_527_);
if (v___x_529_ == 0)
{
uint32_t v___x_530_; uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = 43;
v___x_531_ = lean_unbox_uint32(v_head_491_);
v___x_532_ = lean_uint32_dec_eq(v___x_531_, v___x_530_);
if (v___x_532_ == 0)
{
uint32_t v___x_533_; uint32_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = 45;
v___x_534_ = lean_unbox_uint32(v_head_491_);
v___x_535_ = lean_uint32_dec_eq(v___x_534_, v___x_533_);
if (v___x_535_ == 0)
{
uint32_t v___x_536_; uint32_t v___x_537_; uint8_t v___x_538_; 
v___x_536_ = 46;
v___x_537_ = lean_unbox_uint32(v_head_491_);
v___x_538_ = lean_uint32_dec_eq(v___x_537_, v___x_536_);
if (v___x_538_ == 0)
{
uint32_t v___x_539_; uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_539_ = 94;
v___x_540_ = lean_unbox_uint32(v_head_491_);
v___x_541_ = lean_uint32_dec_eq(v___x_540_, v___x_539_);
if (v___x_541_ == 0)
{
uint32_t v___x_542_; uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = 95;
v___x_543_ = lean_unbox_uint32(v_head_491_);
v___x_544_ = lean_uint32_dec_eq(v___x_543_, v___x_542_);
if (v___x_544_ == 0)
{
uint32_t v___x_545_; uint32_t v___x_546_; uint8_t v___x_547_; 
v___x_545_ = 96;
v___x_546_ = lean_unbox_uint32(v_head_491_);
v___x_547_ = lean_uint32_dec_eq(v___x_546_, v___x_545_);
if (v___x_547_ == 0)
{
uint32_t v___x_548_; uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = 124;
v___x_549_ = lean_unbox_uint32(v_head_491_);
v___x_550_ = lean_uint32_dec_eq(v___x_549_, v___x_548_);
if (v___x_550_ == 0)
{
uint32_t v___x_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = 126;
v___x_552_ = lean_unbox_uint32(v_head_491_);
v___x_553_ = lean_uint32_dec_eq(v___x_552_, v___x_551_);
if (v___x_553_ == 0)
{
uint32_t v___x_554_; uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = 48;
v___x_555_ = lean_unbox_uint32(v_head_491_);
v___x_556_ = lean_uint32_dec_le(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_501_;
}
else
{
uint32_t v___x_557_; uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = 57;
v___x_558_ = lean_unbox_uint32(v_head_491_);
v___x_559_ = lean_uint32_dec_le(v___x_558_, v___x_557_);
if (v___x_559_ == 0)
{
goto v___jp_501_;
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
v___jp_493_:
{
uint32_t v___x_494_; uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = 97;
v___x_495_ = lean_unbox_uint32(v_head_491_);
v___x_496_ = lean_uint32_dec_le(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
return v___x_496_;
}
else
{
uint32_t v___x_497_; uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_497_ = 122;
v___x_498_ = lean_unbox_uint32(v_head_491_);
v___x_499_ = lean_uint32_dec_le(v___x_498_, v___x_497_);
if (v___x_499_ == 0)
{
return v___x_499_;
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
}
v___jp_501_:
{
uint32_t v___x_502_; uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = 65;
v___x_503_ = lean_unbox_uint32(v_head_491_);
v___x_504_ = lean_uint32_dec_le(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
goto v___jp_493_;
}
else
{
uint32_t v___x_505_; uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_505_ = 90;
v___x_506_ = lean_unbox_uint32(v_head_491_);
v___x_507_ = lean_uint32_dec_le(v___x_506_, v___x_505_);
if (v___x_507_ == 0)
{
goto v___jp_493_;
}
else
{
v_x_489_ = v_tail_492_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_isToken_spec__0___boxed(lean_object* v_x_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_x_576_);
lean_dec(v_x_576_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken(lean_object* v_s_579_){
_start:
{
lean_object* v_s_580_; uint8_t v___x_581_; 
v_s_580_ = l_String_toListImpl(v_s_579_);
v___x_581_ = l_List_isEmpty___redArg(v_s_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
v___x_582_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_s_580_);
lean_dec(v_s_580_);
return v___x_582_;
}
else
{
uint8_t v___x_583_; 
lean_dec(v_s_580_);
v___x_583_ = 0;
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object* v_s_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Std_Http_Internal_isToken(v_s_584_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
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
