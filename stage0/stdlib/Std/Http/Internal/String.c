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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__1___boxed(lean_object*, lean_object*);
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
uint8_t v___y_13_; uint8_t v___y_19_; uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 9;
v___x_25_ = lean_uint32_dec_eq(v_c_3_, v___x_24_);
if (v___x_25_ == 0)
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 32;
v___x_27_ = lean_uint32_dec_eq(v_c_3_, v___x_26_);
if (v___x_27_ == 0)
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 33;
v___x_29_ = lean_uint32_dec_eq(v_c_3_, v___x_28_);
if (v___x_29_ == 0)
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 35;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v_c_3_);
if (v___x_31_ == 0)
{
v___y_19_ = v___x_31_;
goto v___jp_18_;
}
else
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 91;
v___x_33_ = lean_uint32_dec_le(v_c_3_, v___x_32_);
v___y_19_ = v___x_33_;
goto v___jp_18_;
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
if (v___y_13_ == 0)
{
uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 34;
v___x_15_ = lean_uint32_dec_eq(v_c_3_, v___x_14_);
if (v___x_15_ == 0)
{
uint32_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 92;
v___x_17_ = lean_uint32_dec_eq(v_c_3_, v___x_16_);
goto v___jp_7_;
}
else
{
goto v___jp_7_;
}
}
else
{
goto v___jp_4_;
}
}
v___jp_18_:
{
if (v___y_19_ == 0)
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 93;
v___x_21_ = lean_uint32_dec_le(v___x_20_, v_c_3_);
if (v___x_21_ == 0)
{
v___y_13_ = v___x_21_;
goto v___jp_12_;
}
else
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 126;
v___x_23_ = lean_uint32_dec_le(v_c_3_, v___x_22_);
v___y_13_ = v___x_23_;
goto v___jp_12_;
}
}
else
{
goto v___jp_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore___redArg___boxed(lean_object* v_c_34_){
_start:
{
uint32_t v_c_boxed_35_; lean_object* v_res_36_; 
v_c_boxed_35_ = lean_unbox_uint32(v_c_34_);
lean_dec(v_c_34_);
v_res_36_ = l_Std_Http_Internal_quoteCore___redArg(v_c_boxed_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteCore(uint32_t v_c_37_, lean_object* v_h_u2080_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Http_Internal_quoteCore___redArg(v_c_37_);
return v___x_39_;
}
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
uint8_t v___x_45_; 
v___x_45_ = 1;
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; uint8_t v___y_49_; uint32_t v___x_65_; uint32_t v___x_66_; uint8_t v___x_67_; 
v_head_46_ = lean_ctor_get(v_x_44_, 0);
v_tail_47_ = lean_ctor_get(v_x_44_, 1);
v___x_65_ = 33;
v___x_66_ = lean_unbox_uint32(v_head_46_);
v___x_67_ = lean_uint32_dec_eq(v___x_66_, v___x_65_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint32_t v___x_69_; uint8_t v___x_70_; 
v___x_68_ = 35;
v___x_69_ = lean_unbox_uint32(v_head_46_);
v___x_70_ = lean_uint32_dec_eq(v___x_69_, v___x_68_);
if (v___x_70_ == 0)
{
uint32_t v___x_71_; uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = 36;
v___x_72_ = lean_unbox_uint32(v_head_46_);
v___x_73_ = lean_uint32_dec_eq(v___x_72_, v___x_71_);
if (v___x_73_ == 0)
{
uint32_t v___x_74_; uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_74_ = 37;
v___x_75_ = lean_unbox_uint32(v_head_46_);
v___x_76_ = lean_uint32_dec_eq(v___x_75_, v___x_74_);
if (v___x_76_ == 0)
{
uint32_t v___x_77_; uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_77_ = 38;
v___x_78_ = lean_unbox_uint32(v_head_46_);
v___x_79_ = lean_uint32_dec_eq(v___x_78_, v___x_77_);
if (v___x_79_ == 0)
{
uint32_t v___x_80_; uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_80_ = 39;
v___x_81_ = lean_unbox_uint32(v_head_46_);
v___x_82_ = lean_uint32_dec_eq(v___x_81_, v___x_80_);
if (v___x_82_ == 0)
{
uint32_t v___x_83_; uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = 42;
v___x_84_ = lean_unbox_uint32(v_head_46_);
v___x_85_ = lean_uint32_dec_eq(v___x_84_, v___x_83_);
if (v___x_85_ == 0)
{
uint32_t v___x_86_; uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_86_ = 43;
v___x_87_ = lean_unbox_uint32(v_head_46_);
v___x_88_ = lean_uint32_dec_eq(v___x_87_, v___x_86_);
if (v___x_88_ == 0)
{
uint32_t v___x_89_; uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_89_ = 45;
v___x_90_ = lean_unbox_uint32(v_head_46_);
v___x_91_ = lean_uint32_dec_eq(v___x_90_, v___x_89_);
if (v___x_91_ == 0)
{
uint32_t v___x_92_; uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_92_ = 46;
v___x_93_ = lean_unbox_uint32(v_head_46_);
v___x_94_ = lean_uint32_dec_eq(v___x_93_, v___x_92_);
if (v___x_94_ == 0)
{
uint32_t v___x_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_95_ = 94;
v___x_96_ = lean_unbox_uint32(v_head_46_);
v___x_97_ = lean_uint32_dec_eq(v___x_96_, v___x_95_);
if (v___x_97_ == 0)
{
uint32_t v___x_98_; uint32_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = 95;
v___x_99_ = lean_unbox_uint32(v_head_46_);
v___x_100_ = lean_uint32_dec_eq(v___x_99_, v___x_98_);
if (v___x_100_ == 0)
{
uint32_t v___x_101_; uint32_t v___x_102_; uint8_t v___x_103_; 
v___x_101_ = 96;
v___x_102_ = lean_unbox_uint32(v_head_46_);
v___x_103_ = lean_uint32_dec_eq(v___x_102_, v___x_101_);
if (v___x_103_ == 0)
{
uint32_t v___x_104_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = 124;
v___x_105_ = lean_unbox_uint32(v_head_46_);
v___x_106_ = lean_uint32_dec_eq(v___x_105_, v___x_104_);
if (v___x_106_ == 0)
{
uint32_t v___x_107_; uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_107_ = 126;
v___x_108_ = lean_unbox_uint32(v_head_46_);
v___x_109_ = lean_uint32_dec_eq(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
uint32_t v___x_110_; uint32_t v___x_111_; uint8_t v___x_112_; 
v___x_110_ = 48;
v___x_111_ = lean_unbox_uint32(v_head_46_);
v___x_112_ = lean_uint32_dec_le(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
{
goto v___jp_58_;
}
else
{
uint32_t v___x_113_; uint32_t v___x_114_; uint8_t v___x_115_; 
v___x_113_ = 57;
v___x_114_ = lean_unbox_uint32(v_head_46_);
v___x_115_ = lean_uint32_dec_le(v___x_114_, v___x_113_);
if (v___x_115_ == 0)
{
goto v___jp_58_;
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
v___jp_48_:
{
if (v___y_49_ == 0)
{
uint32_t v___x_50_; uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_50_ = 97;
v___x_51_ = lean_unbox_uint32(v_head_46_);
v___x_52_ = lean_uint32_dec_le(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
return v___x_52_;
}
else
{
uint32_t v___x_53_; uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_53_ = 122;
v___x_54_ = lean_unbox_uint32(v_head_46_);
v___x_55_ = lean_uint32_dec_le(v___x_54_, v___x_53_);
if (v___x_55_ == 0)
{
return v___x_55_;
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
}
else
{
v_x_44_ = v_tail_47_;
goto _start;
}
}
v___jp_58_:
{
uint32_t v___x_59_; uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_59_ = 65;
v___x_60_ = lean_unbox_uint32(v_head_46_);
v___x_61_ = lean_uint32_dec_le(v___x_59_, v___x_60_);
if (v___x_61_ == 0)
{
v___y_49_ = v___x_61_;
goto v___jp_48_;
}
else
{
uint32_t v___x_62_; uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_62_ = 90;
v___x_63_ = lean_unbox_uint32(v_head_46_);
v___x_64_ = lean_uint32_dec_le(v___x_63_, v___x_62_);
v___y_49_ = v___x_64_;
goto v___jp_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__0(v_x_132_);
lean_dec(v_x_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__1(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
return v_x_135_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; uint32_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_head_137_ = lean_ctor_get(v_x_136_, 0);
v_tail_138_ = lean_ctor_get(v_x_136_, 1);
v___x_139_ = lean_unbox_uint32(v_head_137_);
v___x_140_ = l_Std_Http_Internal_quoteCore___redArg(v___x_139_);
v___x_141_ = lean_string_append(v_x_135_, v___x_140_);
lean_dec_ref(v___x_140_);
v_x_135_ = v___x_141_;
v_x_136_ = v_tail_138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__1___boxed(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__1(v_x_143_, v_x_144_);
lean_dec(v_x_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object* v_s_147_){
_start:
{
lean_object* v_sl_148_; uint8_t v___y_150_; uint8_t v___x_154_; uint8_t v___y_156_; uint8_t v___x_157_; 
lean_inc_ref(v_s_147_);
v_sl_148_ = lean_string_data(v_s_147_);
v___x_154_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__0(v_sl_148_);
v___x_157_ = l_List_isEmpty___redArg(v_sl_148_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 1;
v___y_156_ = v___x_158_;
goto v___jp_155_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
v___y_156_ = v___x_159_;
goto v___jp_155_;
}
v___jp_149_:
{
if (v___y_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v_s_147_);
v___x_151_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString___redArg___closed__0));
v___x_152_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__1(v___x_151_, v_sl_148_);
lean_dec(v_sl_148_);
v___x_153_ = lean_string_append(v___x_152_, v___x_151_);
return v___x_153_;
}
else
{
lean_dec(v_sl_148_);
return v_s_147_;
}
}
v___jp_155_:
{
if (v___x_154_ == 0)
{
v___y_150_ = v___x_154_;
goto v___jp_149_;
}
else
{
v___y_150_ = v___y_156_;
goto v___jp_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object* v_s_160_, lean_object* v_h_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_160_);
return v___x_162_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
else
{
lean_object* v_head_165_; lean_object* v_tail_166_; uint8_t v___y_168_; uint32_t v___x_170_; uint32_t v___x_171_; uint8_t v___x_172_; 
v_head_165_ = lean_ctor_get(v_x_163_, 0);
v_tail_166_ = lean_ctor_get(v_x_163_, 1);
v___x_170_ = 9;
v___x_171_ = lean_unbox_uint32(v_head_165_);
v___x_172_ = lean_uint32_dec_eq(v___x_171_, v___x_170_);
if (v___x_172_ == 0)
{
uint32_t v___x_173_; uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = 32;
v___x_174_ = lean_unbox_uint32(v_head_165_);
v___x_175_ = lean_uint32_dec_eq(v___x_174_, v___x_173_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___y_178_; uint8_t v___y_179_; uint8_t v___y_184_; uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_176_ = 33;
v___x_192_ = lean_unbox_uint32(v_head_165_);
v___x_193_ = lean_uint32_dec_eq(v___x_192_, v___x_176_);
if (v___x_193_ == 0)
{
uint32_t v___x_194_; uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_194_ = 35;
v___x_195_ = lean_unbox_uint32(v_head_165_);
v___x_196_ = lean_uint32_dec_le(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
v___y_184_ = v___x_196_;
goto v___jp_183_;
}
else
{
uint32_t v___x_197_; uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_197_ = 91;
v___x_198_ = lean_unbox_uint32(v_head_165_);
v___x_199_ = lean_uint32_dec_le(v___x_198_, v___x_197_);
v___y_184_ = v___x_199_;
goto v___jp_183_;
}
}
else
{
v_x_163_ = v_tail_166_;
goto _start;
}
v___jp_177_:
{
if (v___y_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unbox_uint32(v_head_165_);
v___x_181_ = lean_uint32_dec_le(v___x_176_, v___x_180_);
if (v___x_181_ == 0)
{
v___y_168_ = v___x_181_;
goto v___jp_167_;
}
else
{
v___y_168_ = v___y_178_;
goto v___jp_167_;
}
}
else
{
v_x_163_ = v_tail_166_;
goto _start;
}
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
uint32_t v___x_185_; uint32_t v___x_186_; uint8_t v___x_187_; uint32_t v___x_188_; uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_185_ = 93;
v___x_186_ = lean_unbox_uint32(v_head_165_);
v___x_187_ = lean_uint32_dec_le(v___x_185_, v___x_186_);
v___x_188_ = 126;
v___x_189_ = lean_unbox_uint32(v_head_165_);
v___x_190_ = lean_uint32_dec_le(v___x_189_, v___x_188_);
if (v___x_187_ == 0)
{
v___y_178_ = v___x_190_;
v___y_179_ = v___x_187_;
goto v___jp_177_;
}
else
{
v___y_178_ = v___x_190_;
v___y_179_ = v___x_190_;
goto v___jp_177_;
}
}
else
{
v_x_163_ = v_tail_166_;
goto _start;
}
}
}
else
{
v_x_163_ = v_tail_166_;
goto _start;
}
}
else
{
v_x_163_ = v_tail_166_;
goto _start;
}
v___jp_167_:
{
if (v___y_168_ == 0)
{
return v___y_168_;
}
else
{
v_x_163_ = v_tail_166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_203_);
lean_dec(v_x_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object* v_s_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
lean_inc_ref(v_s_206_);
v___x_207_ = lean_string_data(v_s_206_);
v___x_208_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v___x_207_);
lean_dec(v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v_s_206_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_206_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object* v_msg_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_214_ = lean_panic_fn_borrowed(v___x_213_, v_msg_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_218_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__2));
v___x_219_ = lean_unsigned_to_nat(12u);
v___x_220_ = lean_unsigned_to_nat(83u);
v___x_221_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__1));
v___x_222_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__0));
v___x_223_ = l_mkPanicMessageWithDecl(v___x_222_, v___x_221_, v___x_220_, v___x_219_, v___x_218_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object* v_s_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_224_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Std_Http_Internal_quoteHttpString_x21___closed__3, &l_Std_Http_Internal_quoteHttpString_x21___closed__3_once, _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3);
v___x_227_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_226_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_225_, 1);
return v_val_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(lean_object* v_x_229_){
_start:
{
switch(lean_obj_tag(v_x_229_))
{
case 0:
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(0u);
return v___x_230_;
}
case 1:
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(1u);
return v___x_231_;
}
case 2:
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(2u);
return v___x_232_;
}
default: 
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(3u);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___boxed(lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(v_x_234_);
lean_dec(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object* v_t_236_, lean_object* v_k_237_){
_start:
{
switch(lean_obj_tag(v_t_236_))
{
case 1:
{
uint8_t v_escaped_238_; lean_object* v_acc_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_escaped_238_ = lean_ctor_get_uint8(v_t_236_, sizeof(void*)*1);
v_acc_239_ = lean_ctor_get(v_t_236_, 0);
lean_inc_ref(v_acc_239_);
lean_dec_ref_known(v_t_236_, 1);
v___x_240_ = lean_box(v_escaped_238_);
v___x_241_ = lean_apply_2(v_k_237_, v___x_240_, v_acc_239_);
return v___x_241_;
}
case 2:
{
lean_object* v_result_242_; lean_object* v___x_243_; 
v_result_242_ = lean_ctor_get(v_t_236_, 0);
lean_inc_ref(v_result_242_);
lean_dec_ref_known(v_t_236_, 1);
v___x_243_ = lean_apply_1(v_k_237_, v_result_242_);
return v___x_243_;
}
default: 
{
lean_dec(v_t_236_);
return v_k_237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object* v_motive_244_, lean_object* v_ctorIdx_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_k_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_246_, v_k_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(v_motive_250_, v_ctorIdx_251_, v_t_252_, v_h_253_, v_k_254_);
lean_dec(v_ctorIdx_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object* v_t_256_, lean_object* v_start_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_256_, v_start_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_start_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_260_, v_start_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object* v_t_264_, lean_object* v_valid_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_264_, v_valid_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object* v_motive_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_valid_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_268_, v_valid_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object* v_t_272_, lean_object* v_done_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_272_, v_done_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_done_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_276_, v_done_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object* v_t_280_, lean_object* v_invalid_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_280_, v_invalid_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object* v_motive_283_, lean_object* v_t_284_, lean_object* v_h_285_, lean_object* v_invalid_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_284_, v_invalid_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object* v_s_288_, lean_object* v_pos_289_){
_start:
{
lean_object* v_str_290_; lean_object* v_startInclusive_291_; lean_object* v_endExclusive_292_; lean_object* v___x_293_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v_decide_304_; 
v_str_290_ = lean_ctor_get(v_s_288_, 0);
v_startInclusive_291_ = lean_ctor_get(v_s_288_, 1);
v_endExclusive_292_ = lean_ctor_get(v_s_288_, 2);
v___x_293_ = lean_nat_add(v_startInclusive_291_, v_pos_289_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_nat_sub(v_endExclusive_292_, v___x_293_);
v_decide_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
lean_dec(v___x_303_);
if (v_decide_304_ == 0)
{
uint32_t v___x_305_; uint8_t v___y_307_; uint32_t v___x_317_; uint8_t v___x_318_; 
v___x_305_ = lean_string_utf8_get_fast(v_str_290_, v___x_293_);
v___x_317_ = 33;
v___x_318_ = lean_uint32_dec_eq(v___x_305_, v___x_317_);
if (v___x_318_ == 0)
{
uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_319_ = 35;
v___x_320_ = lean_uint32_dec_eq(v___x_305_, v___x_319_);
if (v___x_320_ == 0)
{
uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 36;
v___x_322_ = lean_uint32_dec_eq(v___x_305_, v___x_321_);
if (v___x_322_ == 0)
{
uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 37;
v___x_324_ = lean_uint32_dec_eq(v___x_305_, v___x_323_);
if (v___x_324_ == 0)
{
uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 38;
v___x_326_ = lean_uint32_dec_eq(v___x_305_, v___x_325_);
if (v___x_326_ == 0)
{
uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 39;
v___x_328_ = lean_uint32_dec_eq(v___x_305_, v___x_327_);
if (v___x_328_ == 0)
{
uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 42;
v___x_330_ = lean_uint32_dec_eq(v___x_305_, v___x_329_);
if (v___x_330_ == 0)
{
uint32_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = 43;
v___x_332_ = lean_uint32_dec_eq(v___x_305_, v___x_331_);
if (v___x_332_ == 0)
{
uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = 45;
v___x_334_ = lean_uint32_dec_eq(v___x_305_, v___x_333_);
if (v___x_334_ == 0)
{
uint32_t v___x_335_; uint8_t v___x_336_; 
v___x_335_ = 46;
v___x_336_ = lean_uint32_dec_eq(v___x_305_, v___x_335_);
if (v___x_336_ == 0)
{
uint32_t v___x_337_; uint8_t v___x_338_; 
v___x_337_ = 94;
v___x_338_ = lean_uint32_dec_eq(v___x_305_, v___x_337_);
if (v___x_338_ == 0)
{
uint32_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = 95;
v___x_340_ = lean_uint32_dec_eq(v___x_305_, v___x_339_);
if (v___x_340_ == 0)
{
uint32_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 96;
v___x_342_ = lean_uint32_dec_eq(v___x_305_, v___x_341_);
if (v___x_342_ == 0)
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 124;
v___x_344_ = lean_uint32_dec_eq(v___x_305_, v___x_343_);
if (v___x_344_ == 0)
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 126;
v___x_346_ = lean_uint32_dec_eq(v___x_305_, v___x_345_);
if (v___x_346_ == 0)
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 48;
v___x_348_ = lean_uint32_dec_le(v___x_347_, v___x_305_);
if (v___x_348_ == 0)
{
goto v___jp_312_;
}
else
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 57;
v___x_350_ = lean_uint32_dec_le(v___x_305_, v___x_349_);
if (v___x_350_ == 0)
{
goto v___jp_312_;
}
else
{
goto v___jp_294_;
}
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
}
else
{
goto v___jp_294_;
}
v___jp_306_:
{
if (v___y_307_ == 0)
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 97;
v___x_309_ = lean_uint32_dec_le(v___x_308_, v___x_305_);
if (v___x_309_ == 0)
{
lean_dec(v___x_293_);
return v_pos_289_;
}
else
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 122;
v___x_311_ = lean_uint32_dec_le(v___x_305_, v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v___x_293_);
return v_pos_289_;
}
else
{
goto v___jp_294_;
}
}
}
else
{
goto v___jp_294_;
}
}
v___jp_312_:
{
uint32_t v___x_313_; uint8_t v___x_314_; 
v___x_313_ = 65;
v___x_314_ = lean_uint32_dec_le(v___x_313_, v___x_305_);
if (v___x_314_ == 0)
{
v___y_307_ = v___x_314_;
goto v___jp_306_;
}
else
{
uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_315_ = 90;
v___x_316_ = lean_uint32_dec_le(v___x_305_, v___x_315_);
v___y_307_ = v___x_316_;
goto v___jp_306_;
}
}
}
else
{
lean_dec(v___x_293_);
return v_pos_289_;
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_295_ = lean_string_utf8_next_fast(v_str_290_, v___x_293_);
v___x_296_ = lean_nat_sub(v___x_295_, v___x_293_);
lean_dec(v___x_293_);
v___x_297_ = lean_nat_add(v_pos_289_, v___x_296_);
lean_dec(v___x_296_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_pos_289_, v___x_298_);
v___x_300_ = lean_nat_dec_le(v___x_299_, v___x_297_);
lean_dec(v___x_299_);
if (v___x_300_ == 0)
{
lean_dec(v___x_297_);
return v_pos_289_;
}
else
{
lean_dec(v_pos_289_);
v_pos_289_ = v___x_297_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object* v_s_351_, lean_object* v_pos_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v_s_351_, v_pos_352_);
lean_dec_ref(v_s_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(lean_object* v___x_354_, lean_object* v___x_355_, uint32_t v___x_356_, lean_object* v___x_357_, lean_object* v_s_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
uint8_t v_decide_361_; 
v_decide_361_ = lean_nat_dec_eq(v_a_359_, v___x_357_);
if (v_decide_361_ == 0)
{
uint32_t v___x_362_; uint8_t v_decide_363_; uint32_t v___x_364_; lean_object* v___x_365_; 
v___x_362_ = 34;
v_decide_363_ = lean_nat_dec_eq(v___x_354_, v___x_355_);
v___x_364_ = lean_string_utf8_get_fast(v_s_358_, v_a_359_);
v___x_365_ = lean_string_utf8_next_fast(v_s_358_, v_a_359_);
lean_dec(v_a_359_);
switch(lean_obj_tag(v_b_360_))
{
case 0:
{
uint8_t v___x_366_; 
v___x_366_ = lean_uint32_dec_eq(v___x_364_, v___x_362_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(3);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_367_;
goto _start;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_370_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*1, v_decide_363_);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_370_;
goto _start;
}
}
case 1:
{
uint8_t v_escaped_372_; lean_object* v_acc_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_427_; 
v_escaped_372_ = lean_ctor_get_uint8(v_b_360_, sizeof(void*)*1);
v_acc_373_ = lean_ctor_get(v_b_360_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_b_360_);
if (v_isSharedCheck_427_ == 0)
{
v___x_375_ = v_b_360_;
v_isShared_376_ = v_isSharedCheck_427_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_acc_373_);
lean_dec(v_b_360_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_427_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
uint8_t v___y_384_; 
if (v_escaped_372_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
lean_del_object(v___x_375_);
v___x_387_ = 92;
v___x_388_ = lean_uint32_dec_eq(v___x_364_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; uint8_t v___y_395_; uint8_t v___y_399_; 
v___x_389_ = lean_uint32_dec_eq(v___x_364_, v___x_362_);
if (v___x_389_ == 0)
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 9;
v___x_405_ = lean_uint32_dec_eq(v___x_364_, v___x_404_);
if (v___x_405_ == 0)
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 32;
v___x_407_ = lean_uint32_dec_eq(v___x_364_, v___x_406_);
if (v___x_407_ == 0)
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 33;
v___x_409_ = lean_uint32_dec_eq(v___x_364_, v___x_408_);
if (v___x_409_ == 0)
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 35;
v___x_411_ = lean_uint32_dec_le(v___x_410_, v___x_364_);
if (v___x_411_ == 0)
{
v___y_399_ = v___x_411_;
goto v___jp_398_;
}
else
{
uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 91;
v___x_413_ = lean_uint32_dec_le(v___x_364_, v___x_412_);
v___y_399_ = v___x_413_;
goto v___jp_398_;
}
}
else
{
goto v___jp_390_;
}
}
else
{
goto v___jp_390_;
}
}
else
{
goto v___jp_390_;
}
}
else
{
lean_object* v___x_414_; 
v___x_414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_414_, 0, v_acc_373_);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_414_;
goto _start;
}
v___jp_390_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_string_push(v_acc_373_, v___x_364_);
v___x_392_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_389_);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_392_;
goto _start;
}
v___jp_394_:
{
if (v___y_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v_acc_373_);
v___x_396_ = lean_box(3);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_396_;
goto _start;
}
else
{
goto v___jp_390_;
}
}
v___jp_398_:
{
if (v___y_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 93;
v___x_401_ = lean_uint32_dec_le(v___x_400_, v___x_364_);
if (v___x_401_ == 0)
{
v___y_395_ = v___x_401_;
goto v___jp_394_;
}
else
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 126;
v___x_403_ = lean_uint32_dec_le(v___x_364_, v___x_402_);
v___y_395_ = v___x_403_;
goto v___jp_394_;
}
}
else
{
goto v___jp_390_;
}
}
}
else
{
uint8_t v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_uint32_dec_eq(v___x_356_, v___x_362_);
v___x_417_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_417_, 0, v_acc_373_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_416_);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_417_;
goto _start;
}
}
else
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 9;
v___x_420_ = lean_uint32_dec_eq(v___x_364_, v___x_419_);
if (v___x_420_ == 0)
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 32;
v___x_422_ = lean_uint32_dec_eq(v___x_364_, v___x_421_);
if (v___x_422_ == 0)
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 33;
v___x_424_ = lean_uint32_dec_le(v___x_423_, v___x_364_);
if (v___x_424_ == 0)
{
v___y_384_ = v___x_424_;
goto v___jp_383_;
}
else
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 126;
v___x_426_ = lean_uint32_dec_le(v___x_364_, v___x_425_);
v___y_384_ = v___x_426_;
goto v___jp_383_;
}
}
else
{
goto v___jp_377_;
}
}
else
{
goto v___jp_377_;
}
}
v___jp_377_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_string_push(v_acc_373_, v___x_364_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v_decide_363_);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_380_;
goto _start;
}
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v___x_385_; 
lean_del_object(v___x_375_);
lean_dec_ref(v_acc_373_);
v___x_385_ = lean_box(3);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_385_;
goto _start;
}
else
{
goto v___jp_377_;
}
}
}
}
case 2:
{
lean_object* v___x_428_; 
lean_dec_ref_known(v_b_360_, 1);
v___x_428_ = lean_box(3);
v_a_359_ = v___x_365_;
v_b_360_ = v___x_428_;
goto _start;
}
default: 
{
v_a_359_ = v___x_365_;
goto _start;
}
}
}
else
{
lean_dec(v_a_359_);
return v_b_360_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object* v___x_431_, lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v_s_435_, lean_object* v_a_436_, lean_object* v_b_437_){
_start:
{
uint32_t v___x_2367__boxed_438_; lean_object* v_res_439_; 
v___x_2367__boxed_438_ = lean_unbox_uint32(v___x_433_);
lean_dec(v___x_433_);
v_res_439_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_431_, v___x_432_, v___x_2367__boxed_438_, v___x_434_, v_s_435_, v_a_436_, v_b_437_);
lean_dec_ref(v_s_435_);
lean_dec(v___x_434_);
lean_dec(v___x_432_);
lean_dec(v___x_431_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object* v_s_440_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v_decide_451_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_string_utf8_byte_size(v_s_440_);
v_decide_451_ = lean_nat_dec_eq(v___x_449_, v___x_450_);
if (v_decide_451_ == 0)
{
uint32_t v___x_452_; uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_452_ = 34;
v___x_453_ = lean_string_utf8_get_fast(v_s_440_, v___x_449_);
v___x_454_ = lean_uint32_dec_eq(v___x_453_, v___x_452_);
if (v___x_454_ == 0)
{
goto v___jp_441_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc_ref(v_s_440_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v_s_440_);
lean_ctor_set(v___x_455_, 1, v___x_449_);
lean_ctor_set(v___x_455_, 2, v___x_450_);
v___x_456_ = lean_box(0);
v___x_457_ = l_String_Slice_positions(v___x_455_);
lean_dec_ref_known(v___x_455_, 3);
v___x_458_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_449_, v___x_450_, v___x_453_, v___x_450_, v_s_440_, v___x_457_, v___x_456_);
lean_dec_ref(v_s_440_);
if (lean_obj_tag(v___x_458_) == 2)
{
lean_object* v_result_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_result_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_result_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 1);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_result_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_object* v___x_467_; 
lean_dec(v___x_458_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
}
else
{
goto v___jp_441_;
}
v___jp_441_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v_decide_446_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_string_utf8_byte_size(v_s_440_);
lean_inc_ref(v_s_440_);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v_s_440_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
v___x_445_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_444_, v___x_442_);
lean_dec_ref_known(v___x_444_, 3);
v_decide_446_ = lean_nat_dec_eq(v___x_445_, v___x_443_);
lean_dec(v___x_445_);
if (v_decide_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v_s_440_);
v___x_447_ = lean_box(0);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_s_440_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v___x_470_, uint32_t v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_s_474_, lean_object* v_inst_475_, lean_object* v_R_476_, lean_object* v_a_477_, lean_object* v_b_478_, lean_object* v_c_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_469_, v___x_470_, v___x_471_, v___x_473_, v_s_474_, v_a_477_, v_b_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v_s_487_, lean_object* v_inst_488_, lean_object* v_R_489_, lean_object* v_a_490_, lean_object* v_b_491_, lean_object* v_c_492_){
_start:
{
uint32_t v___x_2575__boxed_493_; lean_object* v_res_494_; 
v___x_2575__boxed_493_ = lean_unbox_uint32(v___x_484_);
lean_dec(v___x_484_);
v_res_494_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_481_, v___x_482_, v___x_483_, v___x_2575__boxed_493_, v___x_485_, v___x_486_, v_s_487_, v_inst_488_, v_R_489_, v_a_490_, v_b_491_, v_c_492_);
lean_dec_ref(v_s_487_);
lean_dec(v___x_486_);
lean_dec_ref(v___x_485_);
lean_dec(v___x_483_);
lean_dec(v___x_482_);
lean_dec_ref(v___x_481_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Internal_isToken_spec__0(lean_object* v_x_495_){
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
lean_object* v_head_497_; lean_object* v_tail_498_; uint8_t v___y_500_; uint32_t v___x_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v_head_497_ = lean_ctor_get(v_x_495_, 0);
v_tail_498_ = lean_ctor_get(v_x_495_, 1);
v___x_516_ = 33;
v___x_517_ = lean_unbox_uint32(v_head_497_);
v___x_518_ = lean_uint32_dec_eq(v___x_517_, v___x_516_);
if (v___x_518_ == 0)
{
uint32_t v___x_519_; uint32_t v___x_520_; uint8_t v___x_521_; 
v___x_519_ = 35;
v___x_520_ = lean_unbox_uint32(v_head_497_);
v___x_521_ = lean_uint32_dec_eq(v___x_520_, v___x_519_);
if (v___x_521_ == 0)
{
uint32_t v___x_522_; uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = 36;
v___x_523_ = lean_unbox_uint32(v_head_497_);
v___x_524_ = lean_uint32_dec_eq(v___x_523_, v___x_522_);
if (v___x_524_ == 0)
{
uint32_t v___x_525_; uint32_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = 37;
v___x_526_ = lean_unbox_uint32(v_head_497_);
v___x_527_ = lean_uint32_dec_eq(v___x_526_, v___x_525_);
if (v___x_527_ == 0)
{
uint32_t v___x_528_; uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_528_ = 38;
v___x_529_ = lean_unbox_uint32(v_head_497_);
v___x_530_ = lean_uint32_dec_eq(v___x_529_, v___x_528_);
if (v___x_530_ == 0)
{
uint32_t v___x_531_; uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_531_ = 39;
v___x_532_ = lean_unbox_uint32(v_head_497_);
v___x_533_ = lean_uint32_dec_eq(v___x_532_, v___x_531_);
if (v___x_533_ == 0)
{
uint32_t v___x_534_; uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_534_ = 42;
v___x_535_ = lean_unbox_uint32(v_head_497_);
v___x_536_ = lean_uint32_dec_eq(v___x_535_, v___x_534_);
if (v___x_536_ == 0)
{
uint32_t v___x_537_; uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_537_ = 43;
v___x_538_ = lean_unbox_uint32(v_head_497_);
v___x_539_ = lean_uint32_dec_eq(v___x_538_, v___x_537_);
if (v___x_539_ == 0)
{
uint32_t v___x_540_; uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = 45;
v___x_541_ = lean_unbox_uint32(v_head_497_);
v___x_542_ = lean_uint32_dec_eq(v___x_541_, v___x_540_);
if (v___x_542_ == 0)
{
uint32_t v___x_543_; uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_543_ = 46;
v___x_544_ = lean_unbox_uint32(v_head_497_);
v___x_545_ = lean_uint32_dec_eq(v___x_544_, v___x_543_);
if (v___x_545_ == 0)
{
uint32_t v___x_546_; uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_546_ = 94;
v___x_547_ = lean_unbox_uint32(v_head_497_);
v___x_548_ = lean_uint32_dec_eq(v___x_547_, v___x_546_);
if (v___x_548_ == 0)
{
uint32_t v___x_549_; uint32_t v___x_550_; uint8_t v___x_551_; 
v___x_549_ = 95;
v___x_550_ = lean_unbox_uint32(v_head_497_);
v___x_551_ = lean_uint32_dec_eq(v___x_550_, v___x_549_);
if (v___x_551_ == 0)
{
uint32_t v___x_552_; uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = 96;
v___x_553_ = lean_unbox_uint32(v_head_497_);
v___x_554_ = lean_uint32_dec_eq(v___x_553_, v___x_552_);
if (v___x_554_ == 0)
{
uint32_t v___x_555_; uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 124;
v___x_556_ = lean_unbox_uint32(v_head_497_);
v___x_557_ = lean_uint32_dec_eq(v___x_556_, v___x_555_);
if (v___x_557_ == 0)
{
uint32_t v___x_558_; uint32_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = 126;
v___x_559_ = lean_unbox_uint32(v_head_497_);
v___x_560_ = lean_uint32_dec_eq(v___x_559_, v___x_558_);
if (v___x_560_ == 0)
{
uint32_t v___x_561_; uint32_t v___x_562_; uint8_t v___x_563_; 
v___x_561_ = 48;
v___x_562_ = lean_unbox_uint32(v_head_497_);
v___x_563_ = lean_uint32_dec_le(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
goto v___jp_509_;
}
else
{
uint32_t v___x_564_; uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_564_ = 57;
v___x_565_ = lean_unbox_uint32(v_head_497_);
v___x_566_ = lean_uint32_dec_le(v___x_565_, v___x_564_);
if (v___x_566_ == 0)
{
goto v___jp_509_;
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
if (v___y_500_ == 0)
{
uint32_t v___x_501_; uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_501_ = 97;
v___x_502_ = lean_unbox_uint32(v_head_497_);
v___x_503_ = lean_uint32_dec_le(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
return v___x_503_;
}
else
{
uint32_t v___x_504_; uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_504_ = 122;
v___x_505_ = lean_unbox_uint32(v_head_497_);
v___x_506_ = lean_uint32_dec_le(v___x_505_, v___x_504_);
if (v___x_506_ == 0)
{
return v___x_506_;
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
v___jp_509_:
{
uint32_t v___x_510_; uint32_t v___x_511_; uint8_t v___x_512_; 
v___x_510_ = 65;
v___x_511_ = lean_unbox_uint32(v_head_497_);
v___x_512_ = lean_uint32_dec_le(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
v___y_500_ = v___x_512_;
goto v___jp_499_;
}
else
{
uint32_t v___x_513_; uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = 90;
v___x_514_ = lean_unbox_uint32(v_head_497_);
v___x_515_ = lean_uint32_dec_le(v___x_514_, v___x_513_);
v___y_500_ = v___x_515_;
goto v___jp_499_;
}
}
}
}
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
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken(lean_object* v_s_586_){
_start:
{
lean_object* v_s_587_; uint8_t v___x_588_; 
v_s_587_ = lean_string_data(v_s_586_);
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object* v_s_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Std_Http_Internal_isToken(v_s_591_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal_Char(uint8_t builtin);
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
