// Lean compiler output
// Module: Std.Internal.Http.Internal.String
// Imports: import Init.Grind public import Init.Data.String.TakeDrop public import Std.Internal.Http.Internal.Char
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
uint8_t l_List_all___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Http_Internal_quoteHttpString___redArg___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_quoteHttpString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_quoteHttpString___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_quoteHttpString___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Internal_quoteHttpString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Std_Http_Internal_quoteHttpString___redArg___closed__1 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_quoteHttpString_x3f___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Internal_quoteHttpString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_quoteHttpString_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_quoteHttpString_x3f___closed__0 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Internal_quoteHttpString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Internal.Http.Internal.String"};
static const lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__0 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Internal_quoteHttpString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Http.Internal.quoteHttpString!"};
static const lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__1 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x21___closed__1_value;
static const lean_string_object l_Std_Http_Internal_quoteHttpString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "invalid HTTP quoted-string content"};
static const lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__2 = (const lean_object*)&l_Std_Http_Internal_quoteHttpString_x21___closed__2_value;
static lean_once_cell_t l_Std_Http_Internal_quoteHttpString_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_quoteHttpString_x21___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Internal_isToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_isToken___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_isToken___closed__0 = (const lean_object*)&l_Std_Http_Internal_isToken___closed__0_value;
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
LEAN_EXPORT uint8_t l_Std_Http_Internal_quoteHttpString___redArg___lam__0(uint32_t v_x_42_){
_start:
{
uint8_t v___y_49_; uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 33;
v___x_55_ = lean_uint32_dec_eq(v_x_42_, v___x_54_);
if (v___x_55_ == 0)
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 35;
v___x_57_ = lean_uint32_dec_eq(v_x_42_, v___x_56_);
if (v___x_57_ == 0)
{
uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_58_ = 36;
v___x_59_ = lean_uint32_dec_eq(v_x_42_, v___x_58_);
if (v___x_59_ == 0)
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 37;
v___x_61_ = lean_uint32_dec_eq(v_x_42_, v___x_60_);
if (v___x_61_ == 0)
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 38;
v___x_63_ = lean_uint32_dec_eq(v_x_42_, v___x_62_);
if (v___x_63_ == 0)
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 39;
v___x_65_ = lean_uint32_dec_eq(v_x_42_, v___x_64_);
if (v___x_65_ == 0)
{
uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 42;
v___x_67_ = lean_uint32_dec_eq(v_x_42_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 43;
v___x_69_ = lean_uint32_dec_eq(v_x_42_, v___x_68_);
if (v___x_69_ == 0)
{
uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 45;
v___x_71_ = lean_uint32_dec_eq(v_x_42_, v___x_70_);
if (v___x_71_ == 0)
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 46;
v___x_73_ = lean_uint32_dec_eq(v_x_42_, v___x_72_);
if (v___x_73_ == 0)
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 94;
v___x_75_ = lean_uint32_dec_eq(v_x_42_, v___x_74_);
if (v___x_75_ == 0)
{
uint32_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 95;
v___x_77_ = lean_uint32_dec_eq(v_x_42_, v___x_76_);
if (v___x_77_ == 0)
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 96;
v___x_79_ = lean_uint32_dec_eq(v_x_42_, v___x_78_);
if (v___x_79_ == 0)
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 124;
v___x_81_ = lean_uint32_dec_eq(v_x_42_, v___x_80_);
if (v___x_81_ == 0)
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 126;
v___x_83_ = lean_uint32_dec_eq(v_x_42_, v___x_82_);
if (v___x_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 48;
v___x_85_ = lean_uint32_dec_le(v___x_84_, v_x_42_);
if (v___x_85_ == 0)
{
v___y_49_ = v___x_85_;
goto v___jp_48_;
}
else
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 57;
v___x_87_ = lean_uint32_dec_le(v_x_42_, v___x_86_);
v___y_49_ = v___x_87_;
goto v___jp_48_;
}
}
else
{
return v___x_83_;
}
}
else
{
return v___x_81_;
}
}
else
{
return v___x_79_;
}
}
else
{
return v___x_77_;
}
}
else
{
return v___x_75_;
}
}
else
{
return v___x_73_;
}
}
else
{
return v___x_71_;
}
}
else
{
return v___x_69_;
}
}
else
{
return v___x_67_;
}
}
else
{
return v___x_65_;
}
}
else
{
return v___x_63_;
}
}
else
{
return v___x_61_;
}
}
else
{
return v___x_59_;
}
}
else
{
return v___x_57_;
}
}
else
{
return v___x_55_;
}
v___jp_43_:
{
uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = 97;
v___x_45_ = lean_uint32_dec_le(v___x_44_, v_x_42_);
if (v___x_45_ == 0)
{
return v___x_45_;
}
else
{
uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 122;
v___x_47_ = lean_uint32_dec_le(v_x_42_, v___x_46_);
return v___x_47_;
}
}
v___jp_48_:
{
if (v___y_49_ == 0)
{
uint32_t v___x_50_; uint8_t v___x_51_; 
v___x_50_ = 65;
v___x_51_ = lean_uint32_dec_le(v___x_50_, v_x_42_);
if (v___x_51_ == 0)
{
goto v___jp_43_;
}
else
{
uint32_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = 90;
v___x_53_ = lean_uint32_dec_le(v_x_42_, v___x_52_);
if (v___x_53_ == 0)
{
goto v___jp_43_;
}
else
{
return v___x_53_;
}
}
}
else
{
return v___y_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg___lam__0___boxed(lean_object* v_x_88_){
_start:
{
uint32_t v_x_278__boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_x_278__boxed_89_ = lean_unbox_uint32(v_x_88_);
lean_dec(v_x_88_);
v_res_90_ = l_Std_Http_Internal_quoteHttpString___redArg___lam__0(v_x_278__boxed_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
return v_x_92_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; uint32_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_head_94_ = lean_ctor_get(v_x_93_, 0);
v_tail_95_ = lean_ctor_get(v_x_93_, 1);
v___x_96_ = lean_unbox_uint32(v_head_94_);
v___x_97_ = l_Std_Http_Internal_quoteCore___redArg(v___x_96_);
v___x_98_ = lean_string_append(v_x_92_, v___x_97_);
lean_dec_ref(v___x_97_);
v_x_92_ = v___x_98_;
v_x_93_ = v_tail_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v_x_100_, v_x_101_);
lean_dec(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object* v_s_105_){
_start:
{
lean_object* v___f_106_; lean_object* v_sl_107_; uint8_t v___x_112_; 
v___f_106_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString___redArg___closed__0));
lean_inc_ref(v_s_105_);
v_sl_107_ = lean_string_data(v_s_105_);
lean_inc(v_sl_107_);
v___x_112_ = l_List_all___redArg(v_sl_107_, v___f_106_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_s_105_);
goto v___jp_108_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = l_List_isEmpty___redArg(v_sl_107_);
if (v___x_113_ == 0)
{
lean_dec(v_sl_107_);
return v_s_105_;
}
else
{
lean_dec_ref(v_s_105_);
goto v___jp_108_;
}
}
v___jp_108_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString___redArg___closed__1));
v___x_110_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v___x_109_, v_sl_107_);
lean_dec(v_sl_107_);
v___x_111_ = lean_string_append(v___x_110_, v___x_109_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString(lean_object* v_s_114_, lean_object* v_h_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_114_);
return v___x_116_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_quoteHttpString_x3f___lam__0(uint32_t v___y_117_){
_start:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 9;
v___x_133_ = lean_uint32_dec_eq(v___y_117_, v___x_132_);
if (v___x_133_ == 0)
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 32;
v___x_135_ = lean_uint32_dec_eq(v___y_117_, v___x_134_);
if (v___x_135_ == 0)
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 33;
v___x_137_ = lean_uint32_dec_eq(v___y_117_, v___x_136_);
if (v___x_137_ == 0)
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 35;
v___x_139_ = lean_uint32_dec_le(v___x_138_, v___y_117_);
if (v___x_139_ == 0)
{
goto v___jp_127_;
}
else
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 91;
v___x_141_ = lean_uint32_dec_le(v___y_117_, v___x_140_);
if (v___x_141_ == 0)
{
goto v___jp_127_;
}
else
{
return v___x_141_;
}
}
}
else
{
return v___x_137_;
}
}
else
{
return v___x_135_;
}
}
else
{
return v___x_133_;
}
v___jp_118_:
{
uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = 9;
v___x_120_ = lean_uint32_dec_eq(v___y_117_, v___x_119_);
if (v___x_120_ == 0)
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 32;
v___x_122_ = lean_uint32_dec_eq(v___y_117_, v___x_121_);
if (v___x_122_ == 0)
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 33;
v___x_124_ = lean_uint32_dec_le(v___x_123_, v___y_117_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 126;
v___x_126_ = lean_uint32_dec_le(v___y_117_, v___x_125_);
return v___x_126_;
}
}
else
{
return v___x_122_;
}
}
else
{
return v___x_120_;
}
}
v___jp_127_:
{
uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 93;
v___x_129_ = lean_uint32_dec_le(v___x_128_, v___y_117_);
if (v___x_129_ == 0)
{
goto v___jp_118_;
}
else
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 126;
v___x_131_ = lean_uint32_dec_le(v___y_117_, v___x_130_);
if (v___x_131_ == 0)
{
goto v___jp_118_;
}
else
{
return v___x_131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f___lam__0___boxed(lean_object* v___y_142_){
_start:
{
uint32_t v___y_114__boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v___y_114__boxed_143_ = lean_unbox_uint32(v___y_142_);
lean_dec(v___y_142_);
v_res_144_ = l_Std_Http_Internal_quoteHttpString_x3f___lam__0(v___y_114__boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x3f(lean_object* v_s_147_){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___f_148_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x3f___closed__0));
lean_inc_ref(v_s_147_);
v___x_149_ = lean_string_data(v_s_147_);
v___x_150_ = l_List_all___redArg(v___x_149_, v___f_148_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec_ref(v_s_147_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_147_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(lean_object* v_msg_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_156_ = lean_panic_fn_borrowed(v___x_155_, v_msg_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_160_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__2));
v___x_161_ = lean_unsigned_to_nat(12u);
v___x_162_ = lean_unsigned_to_nat(83u);
v___x_163_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__1));
v___x_164_ = ((lean_object*)(l_Std_Http_Internal_quoteHttpString_x21___closed__0));
v___x_165_ = l_mkPanicMessageWithDecl(v___x_164_, v___x_163_, v___x_162_, v___x_161_, v___x_160_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_quoteHttpString_x21(lean_object* v_s_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&l_Std_Http_Internal_quoteHttpString_x21___closed__3, &l_Std_Http_Internal_quoteHttpString_x21___closed__3_once, _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3);
v___x_169_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_val_170_; 
v_val_170_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_val_170_);
lean_dec_ref(v___x_167_);
return v_val_170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(lean_object* v_x_171_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v___x_172_; 
v___x_172_ = lean_unsigned_to_nat(0u);
return v___x_172_;
}
case 1:
{
lean_object* v___x_173_; 
v___x_173_ = lean_unsigned_to_nat(1u);
return v___x_173_;
}
case 2:
{
lean_object* v___x_174_; 
v___x_174_ = lean_unsigned_to_nat(2u);
return v___x_174_;
}
default: 
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(3u);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___boxed(lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(v_x_176_);
lean_dec(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(lean_object* v_t_178_, lean_object* v_k_179_){
_start:
{
switch(lean_obj_tag(v_t_178_))
{
case 1:
{
uint8_t v_escaped_180_; lean_object* v_acc_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_escaped_180_ = lean_ctor_get_uint8(v_t_178_, sizeof(void*)*1);
v_acc_181_ = lean_ctor_get(v_t_178_, 0);
lean_inc_ref(v_acc_181_);
lean_dec_ref(v_t_178_);
v___x_182_ = lean_box(v_escaped_180_);
v___x_183_ = lean_apply_2(v_k_179_, v___x_182_, v_acc_181_);
return v___x_183_;
}
case 2:
{
lean_object* v_result_184_; lean_object* v___x_185_; 
v_result_184_ = lean_ctor_get(v_t_178_, 0);
lean_inc_ref(v_result_184_);
lean_dec_ref(v_t_178_);
v___x_185_ = lean_apply_1(v_k_179_, v_result_184_);
return v___x_185_;
}
default: 
{
lean_dec(v_t_178_);
return v_k_179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(lean_object* v_motive_186_, lean_object* v_ctorIdx_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_k_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_188_, v_k_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(lean_object* v_motive_192_, lean_object* v_ctorIdx_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_k_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(v_motive_192_, v_ctorIdx_193_, v_t_194_, v_h_195_, v_k_196_);
lean_dec(v_ctorIdx_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(lean_object* v_t_198_, lean_object* v_start_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_198_, v_start_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_start_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_202_, v_start_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(lean_object* v_t_206_, lean_object* v_valid_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_206_, v_valid_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(lean_object* v_motive_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_valid_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_210_, v_valid_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(lean_object* v_t_214_, lean_object* v_done_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_214_, v_done_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_done_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_218_, v_done_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(lean_object* v_t_222_, lean_object* v_invalid_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_222_, v_invalid_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_invalid_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Std_Internal_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(v_t_226_, v_invalid_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(lean_object* v_s_230_, lean_object* v_pos_231_){
_start:
{
lean_object* v_str_232_; lean_object* v_startInclusive_233_; lean_object* v_endExclusive_234_; lean_object* v___x_235_; uint8_t v___y_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_str_232_ = lean_ctor_get(v_s_230_, 0);
v_startInclusive_233_ = lean_ctor_get(v_s_230_, 1);
v_endExclusive_234_ = lean_ctor_get(v_s_230_, 2);
v___x_235_ = lean_nat_add(v_startInclusive_233_, v_pos_231_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_sub(v_endExclusive_234_, v___x_235_);
v___x_246_ = lean_nat_dec_eq(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
uint32_t v___x_247_; uint8_t v___y_254_; uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_247_ = lean_string_utf8_get_fast(v_str_232_, v___x_235_);
v___x_259_ = 33;
v___x_260_ = lean_uint32_dec_eq(v___x_247_, v___x_259_);
if (v___x_260_ == 0)
{
uint32_t v___x_261_; uint8_t v___x_262_; 
v___x_261_ = 35;
v___x_262_ = lean_uint32_dec_eq(v___x_247_, v___x_261_);
if (v___x_262_ == 0)
{
uint32_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 36;
v___x_264_ = lean_uint32_dec_eq(v___x_247_, v___x_263_);
if (v___x_264_ == 0)
{
uint32_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 37;
v___x_266_ = lean_uint32_dec_eq(v___x_247_, v___x_265_);
if (v___x_266_ == 0)
{
uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = 38;
v___x_268_ = lean_uint32_dec_eq(v___x_247_, v___x_267_);
if (v___x_268_ == 0)
{
uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 39;
v___x_270_ = lean_uint32_dec_eq(v___x_247_, v___x_269_);
if (v___x_270_ == 0)
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 42;
v___x_272_ = lean_uint32_dec_eq(v___x_247_, v___x_271_);
if (v___x_272_ == 0)
{
uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 43;
v___x_274_ = lean_uint32_dec_eq(v___x_247_, v___x_273_);
if (v___x_274_ == 0)
{
uint32_t v___x_275_; uint8_t v___x_276_; 
v___x_275_ = 45;
v___x_276_ = lean_uint32_dec_eq(v___x_247_, v___x_275_);
if (v___x_276_ == 0)
{
uint32_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = 46;
v___x_278_ = lean_uint32_dec_eq(v___x_247_, v___x_277_);
if (v___x_278_ == 0)
{
uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = 94;
v___x_280_ = lean_uint32_dec_eq(v___x_247_, v___x_279_);
if (v___x_280_ == 0)
{
uint32_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = 95;
v___x_282_ = lean_uint32_dec_eq(v___x_247_, v___x_281_);
if (v___x_282_ == 0)
{
uint32_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 96;
v___x_284_ = lean_uint32_dec_eq(v___x_247_, v___x_283_);
if (v___x_284_ == 0)
{
uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 124;
v___x_286_ = lean_uint32_dec_eq(v___x_247_, v___x_285_);
if (v___x_286_ == 0)
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 126;
v___x_288_ = lean_uint32_dec_eq(v___x_247_, v___x_287_);
if (v___x_288_ == 0)
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 48;
v___x_290_ = lean_uint32_dec_le(v___x_289_, v___x_247_);
if (v___x_290_ == 0)
{
v___y_254_ = v___x_290_;
goto v___jp_253_;
}
else
{
uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 57;
v___x_292_ = lean_uint32_dec_le(v___x_247_, v___x_291_);
v___y_254_ = v___x_292_;
goto v___jp_253_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
}
else
{
goto v___jp_236_;
}
v___jp_248_:
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 97;
v___x_250_ = lean_uint32_dec_le(v___x_249_, v___x_247_);
if (v___x_250_ == 0)
{
v___y_243_ = v___x_250_;
goto v___jp_242_;
}
else
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 122;
v___x_252_ = lean_uint32_dec_le(v___x_247_, v___x_251_);
v___y_243_ = v___x_252_;
goto v___jp_242_;
}
}
v___jp_253_:
{
if (v___y_254_ == 0)
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 65;
v___x_256_ = lean_uint32_dec_le(v___x_255_, v___x_247_);
if (v___x_256_ == 0)
{
goto v___jp_248_;
}
else
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 90;
v___x_258_ = lean_uint32_dec_le(v___x_247_, v___x_257_);
if (v___x_258_ == 0)
{
goto v___jp_248_;
}
else
{
goto v___jp_236_;
}
}
}
else
{
goto v___jp_236_;
}
}
}
else
{
lean_dec(v___x_235_);
return v_pos_231_;
}
v___jp_236_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_237_ = lean_string_utf8_next_fast(v_str_232_, v___x_235_);
v___x_238_ = lean_nat_sub(v___x_237_, v___x_235_);
lean_dec(v___x_235_);
v___x_239_ = lean_nat_add(v_pos_231_, v___x_238_);
lean_dec(v___x_238_);
v___x_240_ = lean_nat_dec_lt(v_pos_231_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v___x_239_);
return v_pos_231_;
}
else
{
lean_dec(v_pos_231_);
v_pos_231_ = v___x_239_;
goto _start;
}
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
lean_dec(v___x_235_);
return v_pos_231_;
}
else
{
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(lean_object* v_s_293_, lean_object* v_pos_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v_s_293_, v_pos_294_);
lean_dec_ref(v_s_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(uint32_t v___x_296_, lean_object* v___x_297_, lean_object* v_s_298_, lean_object* v_a_299_, lean_object* v_b_300_){
_start:
{
lean_object* v_startInclusive_301_; lean_object* v_endExclusive_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_startInclusive_301_ = lean_ctor_get(v___x_297_, 1);
v_endExclusive_302_ = lean_ctor_get(v___x_297_, 2);
v___x_303_ = lean_nat_sub(v_endExclusive_302_, v_startInclusive_301_);
v___x_304_ = lean_nat_dec_eq(v_a_299_, v___x_303_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
uint32_t v___x_305_; uint32_t v___x_306_; lean_object* v___x_307_; 
v___x_305_ = 34;
v___x_306_ = lean_string_utf8_get_fast(v_s_298_, v_a_299_);
v___x_307_ = lean_string_utf8_next_fast(v_s_298_, v_a_299_);
lean_dec(v_a_299_);
switch(lean_obj_tag(v_b_300_))
{
case 0:
{
uint8_t v___x_314_; 
v___x_314_ = lean_uint32_dec_eq(v___x_306_, v___x_305_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(3);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_315_;
goto _start;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Std_Http_Internal_quoteCore___redArg___closed__0));
v___x_318_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v___x_304_);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_318_;
goto _start;
}
}
case 1:
{
uint8_t v_escaped_320_; lean_object* v_acc_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_366_; 
v_escaped_320_ = lean_ctor_get_uint8(v_b_300_, sizeof(void*)*1);
v_acc_321_ = lean_ctor_get(v_b_300_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_b_300_);
if (v_isSharedCheck_366_ == 0)
{
v___x_323_ = v_b_300_;
v_isShared_324_ = v_isSharedCheck_366_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_acc_321_);
lean_dec(v_b_300_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_366_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
if (v_escaped_320_ == 0)
{
uint32_t v___x_340_; uint8_t v___x_341_; 
lean_del_object(v___x_323_);
v___x_340_ = 92;
v___x_341_ = lean_uint32_dec_eq(v___x_306_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = lean_uint32_dec_eq(v___x_306_, v___x_305_);
if (v___x_342_ == 0)
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 9;
v___x_344_ = lean_uint32_dec_eq(v___x_306_, v___x_343_);
if (v___x_344_ == 0)
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 32;
v___x_346_ = lean_uint32_dec_eq(v___x_306_, v___x_345_);
if (v___x_346_ == 0)
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 33;
v___x_348_ = lean_uint32_dec_eq(v___x_306_, v___x_347_);
if (v___x_348_ == 0)
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 35;
v___x_350_ = lean_uint32_dec_le(v___x_349_, v___x_306_);
if (v___x_350_ == 0)
{
goto v___jp_335_;
}
else
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 91;
v___x_352_ = lean_uint32_dec_le(v___x_306_, v___x_351_);
if (v___x_352_ == 0)
{
goto v___jp_335_;
}
else
{
goto v___jp_331_;
}
}
}
else
{
goto v___jp_331_;
}
}
else
{
goto v___jp_331_;
}
}
else
{
goto v___jp_331_;
}
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_353_, 0, v_acc_321_);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_353_;
goto _start;
}
}
else
{
uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_uint32_dec_eq(v___x_296_, v___x_305_);
v___x_356_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_356_, 0, v_acc_321_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*1, v___x_355_);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_356_;
goto _start;
}
}
else
{
uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_358_ = 9;
v___x_359_ = lean_uint32_dec_eq(v___x_306_, v___x_358_);
if (v___x_359_ == 0)
{
uint32_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = 32;
v___x_361_ = lean_uint32_dec_eq(v___x_306_, v___x_360_);
if (v___x_361_ == 0)
{
uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 33;
v___x_363_ = lean_uint32_dec_le(v___x_362_, v___x_306_);
if (v___x_363_ == 0)
{
lean_del_object(v___x_323_);
lean_dec_ref(v_acc_321_);
goto v___jp_311_;
}
else
{
uint32_t v___x_364_; uint8_t v___x_365_; 
v___x_364_ = 126;
v___x_365_ = lean_uint32_dec_le(v___x_306_, v___x_364_);
if (v___x_365_ == 0)
{
lean_del_object(v___x_323_);
lean_dec_ref(v_acc_321_);
goto v___jp_311_;
}
else
{
goto v___jp_325_;
}
}
}
else
{
goto v___jp_325_;
}
}
else
{
goto v___jp_325_;
}
}
v___jp_325_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_string_push(v_acc_321_, v___x_306_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_304_);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_328_;
goto _start;
}
}
v___jp_331_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_string_push(v_acc_321_, v___x_306_);
v___x_333_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*1, v_escaped_320_);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_333_;
goto _start;
}
v___jp_335_:
{
uint32_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = 93;
v___x_337_ = lean_uint32_dec_le(v___x_336_, v___x_306_);
if (v___x_337_ == 0)
{
lean_dec_ref(v_acc_321_);
goto v___jp_308_;
}
else
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 126;
v___x_339_ = lean_uint32_dec_le(v___x_306_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_acc_321_);
goto v___jp_308_;
}
else
{
goto v___jp_331_;
}
}
}
}
}
case 2:
{
lean_object* v___x_367_; 
lean_dec_ref(v_b_300_);
v___x_367_ = lean_box(3);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_367_;
goto _start;
}
default: 
{
v_a_299_ = v___x_307_;
goto _start;
}
}
v___jp_308_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(3);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_309_;
goto _start;
}
v___jp_311_:
{
lean_object* v___x_312_; 
v___x_312_ = lean_box(3);
v_a_299_ = v___x_307_;
v_b_300_ = v___x_312_;
goto _start;
}
}
else
{
lean_dec(v_a_299_);
return v_b_300_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v_s_372_, lean_object* v_a_373_, lean_object* v_b_374_){
_start:
{
uint32_t v___x_2507__boxed_375_; lean_object* v_res_376_; 
v___x_2507__boxed_375_ = lean_unbox_uint32(v___x_370_);
lean_dec(v___x_370_);
v_res_376_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_2507__boxed_375_, v___x_371_, v_s_372_, v_a_373_, v_b_374_);
lean_dec_ref(v_s_372_);
lean_dec_ref(v___x_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object* v_s_377_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_string_utf8_byte_size(v_s_377_);
v___x_388_ = lean_nat_dec_eq(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
uint32_t v___x_389_; uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_389_ = 34;
v___x_390_ = lean_string_utf8_get_fast(v_s_377_, v___x_386_);
v___x_391_ = lean_uint32_dec_eq(v___x_390_, v___x_389_);
if (v___x_391_ == 0)
{
goto v___jp_378_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc_ref(v_s_377_);
v___x_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_392_, 0, v_s_377_);
lean_ctor_set(v___x_392_, 1, v___x_386_);
lean_ctor_set(v___x_392_, 2, v___x_387_);
v___x_393_ = lean_box(0);
v___x_394_ = l_String_Slice_positions(v___x_392_);
v___x_395_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_390_, v___x_392_, v_s_377_, v___x_394_, v___x_393_);
lean_dec_ref(v_s_377_);
lean_dec_ref(v___x_392_);
if (lean_obj_tag(v___x_395_) == 2)
{
lean_object* v_result_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_result_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_result_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_result_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v___x_404_; 
lean_dec(v___x_395_);
v___x_404_ = lean_box(0);
return v___x_404_;
}
}
}
else
{
goto v___jp_378_;
}
v___jp_378_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_string_utf8_byte_size(v_s_377_);
lean_inc_ref(v_s_377_);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v_s_377_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
v___x_382_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_381_, v___x_379_);
lean_dec_ref(v___x_381_);
v___x_383_ = lean_nat_dec_eq(v___x_382_, v___x_380_);
lean_dec(v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec_ref(v_s_377_);
v___x_384_ = lean_box(0);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_s_377_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(uint32_t v___x_405_, lean_object* v___x_406_, lean_object* v_s_407_, lean_object* v_inst_408_, lean_object* v_R_409_, lean_object* v_a_410_, lean_object* v_b_411_, lean_object* v_c_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_405_, v___x_406_, v_s_407_, v_a_410_, v_b_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_s_416_, lean_object* v_inst_417_, lean_object* v_R_418_, lean_object* v_a_419_, lean_object* v_b_420_, lean_object* v_c_421_){
_start:
{
uint32_t v___x_2702__boxed_422_; lean_object* v_res_423_; 
v___x_2702__boxed_422_ = lean_unbox_uint32(v___x_414_);
lean_dec(v___x_414_);
v_res_423_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(v___x_2702__boxed_422_, v___x_415_, v_s_416_, v_inst_417_, v_R_418_, v_a_419_, v_b_420_, v_c_421_);
lean_dec_ref(v_s_416_);
lean_dec_ref(v___x_415_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken___lam__0(uint32_t v___y_424_){
_start:
{
uint8_t v___y_431_; uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 33;
v___x_437_ = lean_uint32_dec_eq(v___y_424_, v___x_436_);
if (v___x_437_ == 0)
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 35;
v___x_439_ = lean_uint32_dec_eq(v___y_424_, v___x_438_);
if (v___x_439_ == 0)
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 36;
v___x_441_ = lean_uint32_dec_eq(v___y_424_, v___x_440_);
if (v___x_441_ == 0)
{
uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 37;
v___x_443_ = lean_uint32_dec_eq(v___y_424_, v___x_442_);
if (v___x_443_ == 0)
{
uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = 38;
v___x_445_ = lean_uint32_dec_eq(v___y_424_, v___x_444_);
if (v___x_445_ == 0)
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 39;
v___x_447_ = lean_uint32_dec_eq(v___y_424_, v___x_446_);
if (v___x_447_ == 0)
{
uint32_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = 42;
v___x_449_ = lean_uint32_dec_eq(v___y_424_, v___x_448_);
if (v___x_449_ == 0)
{
uint32_t v___x_450_; uint8_t v___x_451_; 
v___x_450_ = 43;
v___x_451_ = lean_uint32_dec_eq(v___y_424_, v___x_450_);
if (v___x_451_ == 0)
{
uint32_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = 45;
v___x_453_ = lean_uint32_dec_eq(v___y_424_, v___x_452_);
if (v___x_453_ == 0)
{
uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_454_ = 46;
v___x_455_ = lean_uint32_dec_eq(v___y_424_, v___x_454_);
if (v___x_455_ == 0)
{
uint32_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 94;
v___x_457_ = lean_uint32_dec_eq(v___y_424_, v___x_456_);
if (v___x_457_ == 0)
{
uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 95;
v___x_459_ = lean_uint32_dec_eq(v___y_424_, v___x_458_);
if (v___x_459_ == 0)
{
uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 96;
v___x_461_ = lean_uint32_dec_eq(v___y_424_, v___x_460_);
if (v___x_461_ == 0)
{
uint32_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 124;
v___x_463_ = lean_uint32_dec_eq(v___y_424_, v___x_462_);
if (v___x_463_ == 0)
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 126;
v___x_465_ = lean_uint32_dec_eq(v___y_424_, v___x_464_);
if (v___x_465_ == 0)
{
uint32_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 48;
v___x_467_ = lean_uint32_dec_le(v___x_466_, v___y_424_);
if (v___x_467_ == 0)
{
v___y_431_ = v___x_467_;
goto v___jp_430_;
}
else
{
uint32_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 57;
v___x_469_ = lean_uint32_dec_le(v___y_424_, v___x_468_);
v___y_431_ = v___x_469_;
goto v___jp_430_;
}
}
else
{
return v___x_465_;
}
}
else
{
return v___x_463_;
}
}
else
{
return v___x_461_;
}
}
else
{
return v___x_459_;
}
}
else
{
return v___x_457_;
}
}
else
{
return v___x_455_;
}
}
else
{
return v___x_453_;
}
}
else
{
return v___x_451_;
}
}
else
{
return v___x_449_;
}
}
else
{
return v___x_447_;
}
}
else
{
return v___x_445_;
}
}
else
{
return v___x_443_;
}
}
else
{
return v___x_441_;
}
}
else
{
return v___x_439_;
}
}
else
{
return v___x_437_;
}
v___jp_425_:
{
uint32_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 97;
v___x_427_ = lean_uint32_dec_le(v___x_426_, v___y_424_);
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 122;
v___x_429_ = lean_uint32_dec_le(v___y_424_, v___x_428_);
return v___x_429_;
}
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 65;
v___x_433_ = lean_uint32_dec_le(v___x_432_, v___y_424_);
if (v___x_433_ == 0)
{
goto v___jp_425_;
}
else
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 90;
v___x_435_ = lean_uint32_dec_le(v___y_424_, v___x_434_);
if (v___x_435_ == 0)
{
goto v___jp_425_;
}
else
{
return v___x_435_;
}
}
}
else
{
return v___y_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___lam__0___boxed(lean_object* v___y_470_){
_start:
{
uint32_t v___y_396__boxed_471_; uint8_t v_res_472_; lean_object* v_r_473_; 
v___y_396__boxed_471_ = lean_unbox_uint32(v___y_470_);
lean_dec(v___y_470_);
v_res_472_ = l_Std_Http_Internal_isToken___lam__0(v___y_396__boxed_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_isToken(lean_object* v_s_475_){
_start:
{
lean_object* v_s_476_; uint8_t v___x_477_; 
v_s_476_ = lean_string_data(v_s_475_);
v___x_477_ = l_List_isEmpty___redArg(v_s_476_);
if (v___x_477_ == 0)
{
lean_object* v___f_478_; uint8_t v___x_479_; 
v___f_478_ = ((lean_object*)(l_Std_Http_Internal_isToken___closed__0));
v___x_479_ = l_List_all___redArg(v_s_476_, v___f_478_);
return v___x_479_;
}
else
{
uint8_t v___x_480_; 
lean_dec(v_s_476_);
v___x_480_ = 0;
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_isToken___boxed(lean_object* v_s_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Std_Http_Internal_isToken(v_s_481_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Internal_Char(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Internal_Char(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Internal_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Internal_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Internal_String(builtin);
}
#ifdef __cplusplus
}
#endif
