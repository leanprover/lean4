// Lean compiler output
// Module: Init.Data.ToString.Name
// Imports: public import Init.Data.String.Substring import Init.Data.String.TakeDrop import Init.Data.String.Search
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
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
extern uint32_t l_Lean_idEndEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_isIdRest___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3;
static const lean_closure_object l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdRest___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4_value;
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0_value;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object*);
static const lean_closure_object l_Lean_Name_escapePart___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdEndEscape___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_escapePart___lam__0___closed__0 = (const lean_object*)&l_Lean_Name_escapePart___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Name_escapePart___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Name_escapePart___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Name_escapePart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_escapePart___lam__0, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_escapePart___closed__0 = (const lean_object*)&l_Lean_Name_escapePart___closed__0_value;
static const lean_closure_object l_Lean_Name_escapePart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Name_escapePart___lam__0___closed__0_value)} };
static const lean_object* l_Lean_Name_escapePart___closed__1 = (const lean_object*)&l_Lean_Name_escapePart___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Name_toStringWithSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Lean_Name_toStringWithSep___closed__0 = (const lean_object*)&l_Lean_Name_toStringWithSep___closed__0_value;
static const lean_closure_object l_Lean_Name_toStringWithSep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_toStringWithSep___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_toStringWithSep___closed__1 = (const lean_object*)&l_Lean_Name_toStringWithSep___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0_value;
static const lean_ctor_object l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1_value;
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2_value;
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_value;
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object*);
static const lean_string_object l_Lean_Name_toStringWithToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Name_toStringWithToken___closed__0 = (const lean_object*)&l_Lean_Name_toStringWithToken___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Name_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_instToString___closed__0 = (const lean_object*)&l_Lean_Name_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Name_instToString = (const lean_object*)&l_Lean_Name_instToString___closed__0_value;
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_string_utf8_byte_size(v_s_1_);
v___x_8_ = lean_nat_dec_lt(v_i_2_, v___x_7_);
if (v___x_8_ == 0)
{
uint8_t v___x_9_; 
lean_dec(v_i_2_);
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v_c_10_; uint8_t v___x_30_; uint8_t v___x_31_; 
lean_inc(v_i_2_);
v_c_10_ = lean_string_get_byte_fast(v_s_1_, v_i_2_);
v___x_30_ = 97;
v___x_31_ = lean_uint8_dec_le(v___x_30_, v_c_10_);
if (v___x_31_ == 0)
{
goto v___jp_25_;
}
else
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 122;
v___x_33_ = lean_uint8_dec_le(v_c_10_, v___x_32_);
if (v___x_33_ == 0)
{
goto v___jp_25_;
}
else
{
goto v___jp_3_;
}
}
v___jp_11_:
{
uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 95;
v___x_13_ = lean_uint8_dec_eq(v_c_10_, v___x_12_);
if (v___x_13_ == 0)
{
uint8_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 39;
v___x_15_ = lean_uint8_dec_eq(v_c_10_, v___x_14_);
if (v___x_15_ == 0)
{
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 33;
v___x_17_ = lean_uint8_dec_eq(v_c_10_, v___x_16_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = 63;
v___x_19_ = lean_uint8_dec_eq(v_c_10_, v___x_18_);
if (v___x_19_ == 0)
{
lean_dec(v_i_2_);
return v___x_19_;
}
else
{
goto v___jp_3_;
}
}
else
{
goto v___jp_3_;
}
}
else
{
goto v___jp_3_;
}
}
else
{
goto v___jp_3_;
}
}
v___jp_20_:
{
uint8_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 48;
v___x_22_ = lean_uint8_dec_le(v___x_21_, v_c_10_);
if (v___x_22_ == 0)
{
goto v___jp_11_;
}
else
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 57;
v___x_24_ = lean_uint8_dec_le(v_c_10_, v___x_23_);
if (v___x_24_ == 0)
{
goto v___jp_11_;
}
else
{
goto v___jp_3_;
}
}
}
v___jp_25_:
{
uint8_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 65;
v___x_27_ = lean_uint8_dec_le(v___x_26_, v_c_10_);
if (v___x_27_ == 0)
{
goto v___jp_20_;
}
else
{
uint8_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 90;
v___x_29_ = lean_uint8_dec_le(v_c_10_, v___x_28_);
if (v___x_29_ == 0)
{
goto v___jp_20_;
}
else
{
goto v___jp_3_;
}
}
}
}
v___jp_3_:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_i_2_, v___x_4_);
lean_dec(v_i_2_);
v_i_2_ = v___x_5_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1_ = stack[0].m_obj;
lean_object* v_i_2_ = stack[1].m_obj;
uint8_t v_res_34_;
v_res_34_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_1_, v_i_2_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_35_, lean_object* v_i_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_35_, v_i_36_);
lean_dec_ref(v_s_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_39_){
_start:
{
lean_object* v___x_43_; uint8_t v_c_44_; uint8_t v___x_53_; uint8_t v___x_54_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v_c_44_ = lean_string_get_byte_fast(v_s_39_, v___x_43_);
v___x_53_ = 97;
v___x_54_ = lean_uint8_dec_le(v___x_53_, v_c_44_);
if (v___x_54_ == 0)
{
goto v___jp_48_;
}
else
{
uint8_t v___x_55_; uint8_t v___x_56_; 
v___x_55_ = 122;
v___x_56_ = lean_uint8_dec_le(v_c_44_, v___x_55_);
if (v___x_56_ == 0)
{
goto v___jp_48_;
}
else
{
goto v___jp_40_;
}
}
v___jp_40_:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_39_, v___x_41_);
return v___x_42_;
}
v___jp_45_:
{
uint8_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 95;
v___x_47_ = lean_uint8_dec_eq(v_c_44_, v___x_46_);
if (v___x_47_ == 0)
{
return v___x_47_;
}
else
{
goto v___jp_40_;
}
}
v___jp_48_:
{
uint8_t v___x_49_; uint8_t v___x_50_; 
v___x_49_ = 65;
v___x_50_ = lean_uint8_dec_le(v___x_49_, v_c_44_);
if (v___x_50_ == 0)
{
goto v___jp_45_;
}
else
{
uint8_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = 90;
v___x_52_ = lean_uint8_dec_le(v_c_44_, v___x_51_);
if (v___x_52_ == 0)
{
goto v___jp_45_;
}
else
{
goto v___jp_40_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_39_ = stack[0].m_obj;
uint8_t v_res_57_;
v_res_57_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_39_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_58_);
lean_dec_ref(v_s_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_61_, lean_object* v_h_62_){
_start:
{
lean_object* v___x_66_; uint8_t v_c_67_; uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v_c_67_ = lean_string_get_byte_fast(v_s_61_, v___x_66_);
v___x_76_ = 97;
v___x_77_ = lean_uint8_dec_le(v___x_76_, v_c_67_);
if (v___x_77_ == 0)
{
goto v___jp_71_;
}
else
{
uint8_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 122;
v___x_79_ = lean_uint8_dec_le(v_c_67_, v___x_78_);
if (v___x_79_ == 0)
{
goto v___jp_71_;
}
else
{
goto v___jp_63_;
}
}
v___jp_63_:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_61_, v___x_64_);
return v___x_65_;
}
v___jp_68_:
{
uint8_t v___x_69_; uint8_t v___x_70_; 
v___x_69_ = 95;
v___x_70_ = lean_uint8_dec_eq(v_c_67_, v___x_69_);
if (v___x_70_ == 0)
{
return v___x_70_;
}
else
{
goto v___jp_63_;
}
}
v___jp_71_:
{
uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 65;
v___x_73_ = lean_uint8_dec_le(v___x_72_, v_c_67_);
if (v___x_73_ == 0)
{
goto v___jp_68_;
}
else
{
uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 90;
v___x_75_ = lean_uint8_dec_le(v_c_67_, v___x_74_);
if (v___x_75_ == 0)
{
goto v___jp_68_;
}
else
{
goto v___jp_63_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_61_ = stack[0].m_obj;
uint8_t v_res_80_;
v_res_80_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(v_s_61_, lean_box(0));
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_81_, lean_object* v_h_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(v_s_81_, v_h_82_);
lean_dec_ref(v_s_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_88_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2));
v___x_89_ = lean_unsigned_to_nat(14u);
v___x_90_ = lean_unsigned_to_nat(22u);
v___x_91_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1));
v___x_92_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_93_ = l_mkPanicMessageWithDecl(v___x_92_, v___x_91_, v___x_90_, v___x_89_, v___x_88_);
return v___x_93_;
}
}
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_95_){
_start:
{
lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v_startInclusive_100_; lean_object* v_endExclusive_101_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; uint32_t v___y_130_; uint32_t v___y_135_; uint32_t v___y_141_; lean_object* v___x_157_; uint8_t v_c_158_; uint8_t v___x_167_; uint8_t v___x_168_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v_c_158_ = lean_string_get_byte_fast(v_s_95_, v___x_157_);
v___x_167_ = 97;
v___x_168_ = lean_uint8_dec_le(v___x_167_, v_c_158_);
if (v___x_168_ == 0)
{
goto v___jp_162_;
}
else
{
uint8_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 122;
v___x_170_ = lean_uint8_dec_le(v_c_158_, v___x_169_);
if (v___x_170_ == 0)
{
goto v___jp_162_;
}
else
{
goto v___jp_154_;
}
}
v___jp_96_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v_decide_105_; 
lean_inc_ref(v___y_98_);
v___x_102_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_98_);
v___x_103_ = l_String_Slice_Pos_skipWhile___redArg(v___y_99_, v___y_97_, v___x_102_);
lean_dec_ref(v___y_99_);
v___x_104_ = lean_nat_sub(v_endExclusive_101_, v_startInclusive_100_);
lean_dec(v_startInclusive_100_);
lean_dec(v_endExclusive_101_);
v_decide_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
lean_dec(v___x_104_);
lean_dec(v___x_103_);
return v_decide_105_;
}
v___jp_106_:
{
if (v___y_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_startInclusive_115_; lean_object* v_endExclusive_116_; 
lean_dec(v___y_111_);
lean_dec(v___y_108_);
lean_dec_ref(v_s_95_);
v___x_113_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_114_ = l_panic___redArg(v___y_107_, v___x_113_);
v_startInclusive_115_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_startInclusive_115_);
v_endExclusive_116_ = lean_ctor_get(v___x_114_, 2);
lean_inc(v_endExclusive_116_);
v___y_97_ = v___y_109_;
v___y_98_ = v___y_110_;
v___y_99_ = v___x_114_;
v_startInclusive_100_ = v_startInclusive_115_;
v_endExclusive_101_ = v_endExclusive_116_;
goto v___jp_96_;
}
else
{
lean_object* v___x_117_; 
lean_inc(v___y_111_);
lean_inc(v___y_108_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_s_95_);
lean_ctor_set(v___x_117_, 1, v___y_108_);
lean_ctor_set(v___x_117_, 2, v___y_111_);
v___y_97_ = v___y_109_;
v___y_98_ = v___y_110_;
v___y_99_ = v___x_117_;
v_startInclusive_100_ = v___y_108_;
v_endExclusive_101_ = v___y_111_;
goto v___jp_96_;
}
}
v___jp_118_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_string_utf8_byte_size(v_s_95_);
lean_inc_ref(v_s_95_);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v_s_95_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = l_Substring_Raw_nextn(v___x_121_, v___x_122_, v___x_119_);
lean_dec_ref_known(v___x_121_, 3);
v___x_124_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_125_ = l_String_instInhabitedSlice;
v___x_126_ = lean_string_is_valid_pos(v_s_95_, v___x_123_);
if (v___x_126_ == 0)
{
v___y_107_ = v___x_125_;
v___y_108_ = v___x_123_;
v___y_109_ = v___x_119_;
v___y_110_ = v___x_124_;
v___y_111_ = v___x_120_;
v___y_112_ = v___x_126_;
goto v___jp_106_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_string_is_valid_pos(v_s_95_, v___x_120_);
if (v___x_127_ == 0)
{
v___y_107_ = v___x_125_;
v___y_108_ = v___x_123_;
v___y_109_ = v___x_119_;
v___y_110_ = v___x_124_;
v___y_111_ = v___x_120_;
v___y_112_ = v___x_127_;
goto v___jp_106_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_le(v___x_123_, v___x_120_);
v___y_107_ = v___x_125_;
v___y_108_ = v___x_123_;
v___y_109_ = v___x_119_;
v___y_110_ = v___x_124_;
v___y_111_ = v___x_120_;
v___y_112_ = v___x_128_;
goto v___jp_106_;
}
}
}
v___jp_129_:
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 95;
v___x_132_ = lean_uint32_dec_eq(v___y_130_, v___x_131_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = l_Lean_isLetterLike(v___y_130_);
if (v___x_133_ == 0)
{
lean_dec_ref(v_s_95_);
return v___x_133_;
}
else
{
goto v___jp_118_;
}
}
else
{
goto v___jp_118_;
}
}
v___jp_134_:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 97;
v___x_137_ = lean_uint32_dec_le(v___x_136_, v___y_135_);
if (v___x_137_ == 0)
{
v___y_130_ = v___y_135_;
goto v___jp_129_;
}
else
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 122;
v___x_139_ = lean_uint32_dec_le(v___y_135_, v___x_138_);
if (v___x_139_ == 0)
{
v___y_130_ = v___y_135_;
goto v___jp_129_;
}
else
{
goto v___jp_118_;
}
}
}
v___jp_140_:
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 65;
v___x_143_ = lean_uint32_dec_le(v___x_142_, v___y_141_);
if (v___x_143_ == 0)
{
v___y_135_ = v___y_141_;
goto v___jp_134_;
}
else
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 90;
v___x_145_ = lean_uint32_dec_le(v___y_141_, v___x_144_);
if (v___x_145_ == 0)
{
v___y_135_ = v___y_141_;
goto v___jp_134_;
}
else
{
goto v___jp_118_;
}
}
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_string_utf8_byte_size(v_s_95_);
lean_inc_ref(v_s_95_);
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v_s_95_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
v___x_150_ = l_String_Slice_Pos_get_x3f(v___x_149_, v___x_147_);
lean_dec_ref_known(v___x_149_, 3);
if (lean_obj_tag(v___x_150_) == 0)
{
uint32_t v___x_151_; 
v___x_151_ = 65;
v___y_141_ = v___x_151_;
goto v___jp_140_;
}
else
{
lean_object* v_val_152_; uint32_t v___x_153_; 
v_val_152_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_150_, 1);
v___x_153_ = lean_unbox_uint32(v_val_152_);
lean_dec(v_val_152_);
v___y_141_ = v___x_153_;
goto v___jp_140_;
}
}
v___jp_154_:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_95_, v___x_155_);
if (v___x_156_ == 0)
{
goto v___jp_146_;
}
else
{
lean_dec_ref(v_s_95_);
return v___x_156_;
}
}
v___jp_159_:
{
uint8_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 95;
v___x_161_ = lean_uint8_dec_eq(v_c_158_, v___x_160_);
if (v___x_161_ == 0)
{
goto v___jp_146_;
}
else
{
goto v___jp_154_;
}
}
v___jp_162_:
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 65;
v___x_164_ = lean_uint8_dec_le(v___x_163_, v_c_158_);
if (v___x_164_ == 0)
{
goto v___jp_159_;
}
else
{
uint8_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 90;
v___x_166_ = lean_uint8_dec_le(v_c_158_, v___x_165_);
if (v___x_166_ == 0)
{
goto v___jp_159_;
}
else
{
goto v___jp_154_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_95_ = stack[0].m_obj;
uint8_t v_res_171_;
v_res_171_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_95_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_175_, lean_object* v_h_176_){
_start:
{
lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v_startInclusive_181_; lean_object* v_endExclusive_182_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; uint32_t v___y_211_; uint32_t v___y_216_; uint32_t v___y_222_; lean_object* v___x_238_; uint8_t v_c_239_; uint8_t v___x_248_; uint8_t v___x_249_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v_c_239_ = lean_string_get_byte_fast(v_s_175_, v___x_238_);
v___x_248_ = 97;
v___x_249_ = lean_uint8_dec_le(v___x_248_, v_c_239_);
if (v___x_249_ == 0)
{
goto v___jp_243_;
}
else
{
uint8_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 122;
v___x_251_ = lean_uint8_dec_le(v_c_239_, v___x_250_);
if (v___x_251_ == 0)
{
goto v___jp_243_;
}
else
{
goto v___jp_235_;
}
}
v___jp_177_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v_decide_186_; 
lean_inc_ref(v___y_179_);
v___x_183_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_179_);
v___x_184_ = l_String_Slice_Pos_skipWhile___redArg(v___y_180_, v___y_178_, v___x_183_);
lean_dec_ref(v___y_180_);
v___x_185_ = lean_nat_sub(v_endExclusive_182_, v_startInclusive_181_);
lean_dec(v_startInclusive_181_);
lean_dec(v_endExclusive_182_);
v_decide_186_ = lean_nat_dec_eq(v___x_184_, v___x_185_);
lean_dec(v___x_185_);
lean_dec(v___x_184_);
return v_decide_186_;
}
v___jp_187_:
{
if (v___y_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_startInclusive_196_; lean_object* v_endExclusive_197_; 
lean_dec(v___y_192_);
lean_dec(v___y_189_);
lean_dec_ref(v_s_175_);
v___x_194_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_195_ = l_panic___redArg(v___y_188_, v___x_194_);
v_startInclusive_196_ = lean_ctor_get(v___x_195_, 1);
lean_inc(v_startInclusive_196_);
v_endExclusive_197_ = lean_ctor_get(v___x_195_, 2);
lean_inc(v_endExclusive_197_);
v___y_178_ = v___y_190_;
v___y_179_ = v___y_191_;
v___y_180_ = v___x_195_;
v_startInclusive_181_ = v_startInclusive_196_;
v_endExclusive_182_ = v_endExclusive_197_;
goto v___jp_177_;
}
else
{
lean_object* v___x_198_; 
lean_inc(v___y_192_);
lean_inc(v___y_189_);
v___x_198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_198_, 0, v_s_175_);
lean_ctor_set(v___x_198_, 1, v___y_189_);
lean_ctor_set(v___x_198_, 2, v___y_192_);
v___y_178_ = v___y_190_;
v___y_179_ = v___y_191_;
v___y_180_ = v___x_198_;
v_startInclusive_181_ = v___y_189_;
v_endExclusive_182_ = v___y_192_;
goto v___jp_177_;
}
}
v___jp_199_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_string_utf8_byte_size(v_s_175_);
lean_inc_ref(v_s_175_);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_s_175_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_201_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = l_Substring_Raw_nextn(v___x_202_, v___x_203_, v___x_200_);
lean_dec_ref_known(v___x_202_, 3);
v___x_205_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_206_ = l_String_instInhabitedSlice;
v___x_207_ = lean_string_is_valid_pos(v_s_175_, v___x_204_);
if (v___x_207_ == 0)
{
v___y_188_ = v___x_206_;
v___y_189_ = v___x_204_;
v___y_190_ = v___x_200_;
v___y_191_ = v___x_205_;
v___y_192_ = v___x_201_;
v___y_193_ = v___x_207_;
goto v___jp_187_;
}
else
{
uint8_t v___x_208_; 
v___x_208_ = lean_string_is_valid_pos(v_s_175_, v___x_201_);
if (v___x_208_ == 0)
{
v___y_188_ = v___x_206_;
v___y_189_ = v___x_204_;
v___y_190_ = v___x_200_;
v___y_191_ = v___x_205_;
v___y_192_ = v___x_201_;
v___y_193_ = v___x_208_;
goto v___jp_187_;
}
else
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_le(v___x_204_, v___x_201_);
v___y_188_ = v___x_206_;
v___y_189_ = v___x_204_;
v___y_190_ = v___x_200_;
v___y_191_ = v___x_205_;
v___y_192_ = v___x_201_;
v___y_193_ = v___x_209_;
goto v___jp_187_;
}
}
}
v___jp_210_:
{
uint32_t v___x_212_; uint8_t v___x_213_; 
v___x_212_ = 95;
v___x_213_ = lean_uint32_dec_eq(v___y_211_, v___x_212_);
if (v___x_213_ == 0)
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_isLetterLike(v___y_211_);
if (v___x_214_ == 0)
{
lean_dec_ref(v_s_175_);
return v___x_214_;
}
else
{
goto v___jp_199_;
}
}
else
{
goto v___jp_199_;
}
}
v___jp_215_:
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 97;
v___x_218_ = lean_uint32_dec_le(v___x_217_, v___y_216_);
if (v___x_218_ == 0)
{
v___y_211_ = v___y_216_;
goto v___jp_210_;
}
else
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 122;
v___x_220_ = lean_uint32_dec_le(v___y_216_, v___x_219_);
if (v___x_220_ == 0)
{
v___y_211_ = v___y_216_;
goto v___jp_210_;
}
else
{
goto v___jp_199_;
}
}
}
v___jp_221_:
{
uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 65;
v___x_224_ = lean_uint32_dec_le(v___x_223_, v___y_222_);
if (v___x_224_ == 0)
{
v___y_216_ = v___y_222_;
goto v___jp_215_;
}
else
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 90;
v___x_226_ = lean_uint32_dec_le(v___y_222_, v___x_225_);
if (v___x_226_ == 0)
{
v___y_216_ = v___y_222_;
goto v___jp_215_;
}
else
{
goto v___jp_199_;
}
}
}
v___jp_227_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_string_utf8_byte_size(v_s_175_);
lean_inc_ref(v_s_175_);
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v_s_175_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
v___x_231_ = l_String_Slice_Pos_get_x3f(v___x_230_, v___x_228_);
lean_dec_ref_known(v___x_230_, 3);
if (lean_obj_tag(v___x_231_) == 0)
{
uint32_t v___x_232_; 
v___x_232_ = 65;
v___y_222_ = v___x_232_;
goto v___jp_221_;
}
else
{
lean_object* v_val_233_; uint32_t v___x_234_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_231_, 1);
v___x_234_ = lean_unbox_uint32(v_val_233_);
lean_dec(v_val_233_);
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
}
v___jp_235_:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_175_, v___x_236_);
if (v___x_237_ == 0)
{
goto v___jp_227_;
}
else
{
lean_dec_ref(v_s_175_);
return v___x_237_;
}
}
v___jp_240_:
{
uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 95;
v___x_242_ = lean_uint8_dec_eq(v_c_239_, v___x_241_);
if (v___x_242_ == 0)
{
goto v___jp_227_;
}
else
{
goto v___jp_235_;
}
}
v___jp_243_:
{
uint8_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 65;
v___x_245_ = lean_uint8_dec_le(v___x_244_, v_c_239_);
if (v___x_245_ == 0)
{
goto v___jp_240_;
}
else
{
uint8_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 90;
v___x_247_ = lean_uint8_dec_le(v_c_239_, v___x_246_);
if (v___x_247_ == 0)
{
goto v___jp_240_;
}
else
{
goto v___jp_235_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_175_ = stack[0].m_obj;
uint8_t v_res_252_;
v_res_252_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_175_, lean_box(0));
stack->m_num = v_res_252_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_253_, lean_object* v_h_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_253_, v_h_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = l_Lean_idBeginEscape;
v___x_259_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_260_ = lean_string_push(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_idEndEscape;
v___x_262_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_263_ = lean_string_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_266_ = lean_string_append(v___x_265_, v_s_264_);
v___x_267_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_269_);
lean_dec_ref(v_s_269_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_273_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_282_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_274_, v___x_281_, v___y_275_, lean_box(0), lean_box(0), v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
lean_object* l_Lean_Name_escapePart(lean_object* v_s_286_, uint8_t v_force_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_string_utf8_byte_size(v_s_286_);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_291_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_292_ = lean_string_append(v___x_291_, v_s_286_);
lean_dec_ref(v_s_286_);
v___x_293_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v___f_296_; uint8_t v___y_308_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v_startInclusive_314_; lean_object* v_endExclusive_315_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; uint8_t v___y_326_; uint32_t v___y_342_; uint32_t v___y_347_; uint32_t v___y_353_; 
v___f_296_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_287_ == 0)
{
uint8_t v_c_367_; uint8_t v___x_376_; uint8_t v___x_377_; 
v_c_367_ = lean_string_get_byte_fast(v_s_286_, v___x_288_);
v___x_376_ = 97;
v___x_377_ = lean_uint8_dec_le(v___x_376_, v_c_367_);
if (v___x_377_ == 0)
{
goto v___jp_371_;
}
else
{
uint8_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 122;
v___x_379_ = lean_uint8_dec_le(v_c_367_, v___x_378_);
if (v___x_379_ == 0)
{
goto v___jp_371_;
}
else
{
goto v___jp_364_;
}
}
v___jp_368_:
{
uint8_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 95;
v___x_370_ = lean_uint8_dec_eq(v_c_367_, v___x_369_);
if (v___x_370_ == 0)
{
goto v___jp_358_;
}
else
{
goto v___jp_364_;
}
}
v___jp_371_:
{
uint8_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = 65;
v___x_373_ = lean_uint8_dec_le(v___x_372_, v_c_367_);
if (v___x_373_ == 0)
{
goto v___jp_368_;
}
else
{
uint8_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 90;
v___x_375_ = lean_uint8_dec_le(v_c_367_, v___x_374_);
if (v___x_375_ == 0)
{
goto v___jp_368_;
}
else
{
goto v___jp_364_;
}
}
}
}
else
{
goto v___jp_297_;
}
v___jp_297_:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_286_);
v___x_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_299_, 0, v_s_286_);
lean_ctor_set(v___x_299_, 1, v___x_288_);
lean_ctor_set(v___x_299_, 2, v___x_289_);
v___x_300_ = l_String_Slice_contains___redArg(v___f_296_, v___x_299_, v___x_298_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_301_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_302_ = lean_string_append(v___x_301_, v_s_286_);
lean_dec_ref(v_s_286_);
v___x_303_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec_ref(v_s_286_);
v___x_306_ = lean_box(0);
return v___x_306_;
}
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
goto v___jp_297_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v_s_286_);
return v___x_309_;
}
}
v___jp_310_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v_decide_319_; 
lean_inc_ref(v___y_311_);
v___x_316_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_311_);
v___x_317_ = l_String_Slice_Pos_skipWhile___redArg(v___y_313_, v___y_312_, v___x_316_);
lean_dec_ref(v___y_313_);
v___x_318_ = lean_nat_sub(v_endExclusive_315_, v_startInclusive_314_);
lean_dec(v_startInclusive_314_);
lean_dec(v_endExclusive_315_);
v_decide_319_ = lean_nat_dec_eq(v___x_317_, v___x_318_);
lean_dec(v___x_318_);
lean_dec(v___x_317_);
v___y_308_ = v_decide_319_;
goto v___jp_307_;
}
v___jp_320_:
{
if (v___y_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_startInclusive_329_; lean_object* v_endExclusive_330_; 
lean_dec(v___y_325_);
lean_dec(v___y_323_);
v___x_327_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_328_ = l_panic___redArg(v___y_324_, v___x_327_);
v_startInclusive_329_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_startInclusive_329_);
v_endExclusive_330_ = lean_ctor_get(v___x_328_, 2);
lean_inc(v_endExclusive_330_);
v___y_311_ = v___y_321_;
v___y_312_ = v___y_322_;
v___y_313_ = v___x_328_;
v_startInclusive_314_ = v_startInclusive_329_;
v_endExclusive_315_ = v_endExclusive_330_;
goto v___jp_310_;
}
else
{
lean_object* v___x_331_; 
lean_inc(v___y_325_);
lean_inc(v___y_323_);
lean_inc_ref(v_s_286_);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v_s_286_);
lean_ctor_set(v___x_331_, 1, v___y_323_);
lean_ctor_set(v___x_331_, 2, v___y_325_);
v___y_311_ = v___y_321_;
v___y_312_ = v___y_322_;
v___y_313_ = v___x_331_;
v_startInclusive_314_ = v___y_323_;
v_endExclusive_315_ = v___y_325_;
goto v___jp_310_;
}
}
v___jp_332_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
lean_inc_ref(v_s_286_);
v___x_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_333_, 0, v_s_286_);
lean_ctor_set(v___x_333_, 1, v___x_288_);
lean_ctor_set(v___x_333_, 2, v___x_289_);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = l_Substring_Raw_nextn(v___x_333_, v___x_334_, v___x_288_);
lean_dec_ref_known(v___x_333_, 3);
v___x_336_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_337_ = l_String_instInhabitedSlice;
v___x_338_ = lean_string_is_valid_pos(v_s_286_, v___x_335_);
if (v___x_338_ == 0)
{
v___y_321_ = v___x_336_;
v___y_322_ = v___x_288_;
v___y_323_ = v___x_335_;
v___y_324_ = v___x_337_;
v___y_325_ = v___x_289_;
v___y_326_ = v___x_338_;
goto v___jp_320_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = lean_string_is_valid_pos(v_s_286_, v___x_289_);
if (v___x_339_ == 0)
{
v___y_321_ = v___x_336_;
v___y_322_ = v___x_288_;
v___y_323_ = v___x_335_;
v___y_324_ = v___x_337_;
v___y_325_ = v___x_289_;
v___y_326_ = v___x_339_;
goto v___jp_320_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = lean_nat_dec_le(v___x_335_, v___x_289_);
v___y_321_ = v___x_336_;
v___y_322_ = v___x_288_;
v___y_323_ = v___x_335_;
v___y_324_ = v___x_337_;
v___y_325_ = v___x_289_;
v___y_326_ = v___x_340_;
goto v___jp_320_;
}
}
}
v___jp_341_:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 95;
v___x_344_ = lean_uint32_dec_eq(v___y_342_, v___x_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_isLetterLike(v___y_342_);
if (v___x_345_ == 0)
{
v___y_308_ = v___x_345_;
goto v___jp_307_;
}
else
{
goto v___jp_332_;
}
}
else
{
goto v___jp_332_;
}
}
v___jp_346_:
{
uint32_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = 97;
v___x_349_ = lean_uint32_dec_le(v___x_348_, v___y_347_);
if (v___x_349_ == 0)
{
v___y_342_ = v___y_347_;
goto v___jp_341_;
}
else
{
uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 122;
v___x_351_ = lean_uint32_dec_le(v___y_347_, v___x_350_);
if (v___x_351_ == 0)
{
v___y_342_ = v___y_347_;
goto v___jp_341_;
}
else
{
goto v___jp_332_;
}
}
}
v___jp_352_:
{
uint32_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = 65;
v___x_355_ = lean_uint32_dec_le(v___x_354_, v___y_353_);
if (v___x_355_ == 0)
{
v___y_347_ = v___y_353_;
goto v___jp_346_;
}
else
{
uint32_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = 90;
v___x_357_ = lean_uint32_dec_le(v___y_353_, v___x_356_);
if (v___x_357_ == 0)
{
v___y_347_ = v___y_353_;
goto v___jp_346_;
}
else
{
goto v___jp_332_;
}
}
}
v___jp_358_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_inc_ref(v_s_286_);
v___x_359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_359_, 0, v_s_286_);
lean_ctor_set(v___x_359_, 1, v___x_288_);
lean_ctor_set(v___x_359_, 2, v___x_289_);
v___x_360_ = l_String_Slice_Pos_get_x3f(v___x_359_, v___x_288_);
lean_dec_ref_known(v___x_359_, 3);
if (lean_obj_tag(v___x_360_) == 0)
{
uint32_t v___x_361_; 
v___x_361_ = 65;
v___y_353_ = v___x_361_;
goto v___jp_352_;
}
else
{
lean_object* v_val_362_; uint32_t v___x_363_; 
v_val_362_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_val_362_);
lean_dec_ref_known(v___x_360_, 1);
v___x_363_ = lean_unbox_uint32(v_val_362_);
lean_dec(v_val_362_);
v___y_353_ = v___x_363_;
goto v___jp_352_;
}
}
v___jp_364_:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_286_, v___x_365_);
if (v___x_366_ == 0)
{
goto v___jp_358_;
}
else
{
v___y_308_ = v___x_366_;
goto v___jp_307_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Name_escapePart_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_286_ = stack[0].m_obj;
uint8_t v_force_287_ = stack[1].m_num;
lean_object* v_res_380_;
v_res_380_ = l_Lean_Name_escapePart(v_s_286_, v_force_287_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_381_, lean_object* v_force_382_){
_start:
{
uint8_t v_force_boxed_383_; lean_object* v_res_384_; 
v_force_boxed_383_ = lean_unbox(v_force_382_);
v_res_384_ = l_Lean_Name_escapePart(v_s_381_, v_force_boxed_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = l_String_instInhabitedSlice;
v___x_387_ = lean_panic_fn_borrowed(v___x_386_, v_msg_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_388_, lean_object* v_pos_389_){
_start:
{
lean_object* v_str_390_; lean_object* v_startInclusive_391_; lean_object* v_endExclusive_392_; lean_object* v___x_393_; uint8_t v___y_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v_decide_406_; 
v_str_390_ = lean_ctor_get(v_s_388_, 0);
v_startInclusive_391_ = lean_ctor_get(v_s_388_, 1);
v_endExclusive_392_ = lean_ctor_get(v_s_388_, 2);
v___x_393_ = lean_nat_add(v_startInclusive_391_, v_pos_389_);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_nat_sub(v_endExclusive_392_, v___x_393_);
v_decide_406_ = lean_nat_dec_eq(v___x_404_, v___x_405_);
lean_dec(v___x_405_);
if (v_decide_406_ == 0)
{
uint32_t v___x_407_; uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_407_ = lean_string_utf8_get_fast(v_str_390_, v___x_393_);
v___x_429_ = 65;
v___x_430_ = lean_uint32_dec_le(v___x_429_, v___x_407_);
if (v___x_430_ == 0)
{
goto v___jp_424_;
}
else
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 90;
v___x_432_ = lean_uint32_dec_le(v___x_407_, v___x_431_);
if (v___x_432_ == 0)
{
goto v___jp_424_;
}
else
{
goto v___jp_394_;
}
}
v___jp_408_:
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 95;
v___x_410_ = lean_uint32_dec_eq(v___x_407_, v___x_409_);
if (v___x_410_ == 0)
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 39;
v___x_412_ = lean_uint32_dec_eq(v___x_407_, v___x_411_);
if (v___x_412_ == 0)
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 33;
v___x_414_ = lean_uint32_dec_eq(v___x_407_, v___x_413_);
if (v___x_414_ == 0)
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 63;
v___x_416_ = lean_uint32_dec_eq(v___x_407_, v___x_415_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = l_Lean_isLetterLike(v___x_407_);
if (v___x_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = l_Lean_isSubScriptAlnum(v___x_407_);
v___y_403_ = v___x_418_;
goto v___jp_402_;
}
else
{
v___y_403_ = v___x_417_;
goto v___jp_402_;
}
}
else
{
goto v___jp_394_;
}
}
else
{
goto v___jp_394_;
}
}
else
{
goto v___jp_394_;
}
}
else
{
goto v___jp_394_;
}
}
v___jp_419_:
{
uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 48;
v___x_421_ = lean_uint32_dec_le(v___x_420_, v___x_407_);
if (v___x_421_ == 0)
{
goto v___jp_408_;
}
else
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 57;
v___x_423_ = lean_uint32_dec_le(v___x_407_, v___x_422_);
if (v___x_423_ == 0)
{
goto v___jp_408_;
}
else
{
goto v___jp_394_;
}
}
}
v___jp_424_:
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 97;
v___x_426_ = lean_uint32_dec_le(v___x_425_, v___x_407_);
if (v___x_426_ == 0)
{
goto v___jp_419_;
}
else
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 122;
v___x_428_ = lean_uint32_dec_le(v___x_407_, v___x_427_);
if (v___x_428_ == 0)
{
goto v___jp_419_;
}
else
{
goto v___jp_394_;
}
}
}
}
else
{
lean_dec(v___x_393_);
return v_pos_389_;
}
v___jp_394_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_395_ = lean_string_utf8_next_fast(v_str_390_, v___x_393_);
v___x_396_ = lean_nat_sub(v___x_395_, v___x_393_);
lean_dec(v___x_393_);
v___x_397_ = lean_nat_add(v_pos_389_, v___x_396_);
lean_dec(v___x_396_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_pos_389_, v___x_398_);
v___x_400_ = lean_nat_dec_le(v___x_399_, v___x_397_);
lean_dec(v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v___x_397_);
return v_pos_389_;
}
else
{
lean_dec(v_pos_389_);
v_pos_389_ = v___x_397_;
goto _start;
}
}
v___jp_402_:
{
if (v___y_403_ == 0)
{
lean_dec(v___x_393_);
return v_pos_389_;
}
else
{
goto v___jp_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_433_, lean_object* v_pos_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_433_, v_pos_434_);
lean_dec_ref(v_s_433_);
return v_res_435_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_436_, lean_object* v_a_437_, uint8_t v_b_438_){
_start:
{
lean_object* v_str_439_; lean_object* v_startInclusive_440_; lean_object* v_endExclusive_441_; lean_object* v___x_442_; uint8_t v_decide_443_; 
v_str_439_ = lean_ctor_get(v_s_436_, 0);
v_startInclusive_440_ = lean_ctor_get(v_s_436_, 1);
v_endExclusive_441_ = lean_ctor_get(v_s_436_, 2);
v___x_442_ = lean_nat_sub(v_endExclusive_441_, v_startInclusive_440_);
v_decide_443_ = lean_nat_dec_eq(v_a_437_, v___x_442_);
lean_dec(v___x_442_);
if (v_decide_443_ == 0)
{
lean_object* v___x_444_; uint32_t v___x_445_; uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_444_ = lean_nat_add(v_startInclusive_440_, v_a_437_);
lean_dec(v_a_437_);
v___x_445_ = lean_string_utf8_get_fast(v_str_439_, v___x_444_);
v___x_446_ = l_Lean_idEndEscape;
v___x_447_ = lean_uint32_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_string_utf8_next_fast(v_str_439_, v___x_444_);
lean_dec(v___x_444_);
v___x_449_ = lean_nat_sub(v___x_448_, v_startInclusive_440_);
v_a_437_ = v___x_449_;
v_b_438_ = v___x_447_;
goto _start;
}
else
{
lean_dec(v___x_444_);
return v___x_447_;
}
}
else
{
lean_dec(v_a_437_);
return v_b_438_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_436_ = stack[0].m_obj;
lean_object* v_a_437_ = stack[1].m_obj;
uint8_t v_b_438_ = stack[2].m_num;
uint8_t v_res_451_;
v_res_451_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_436_, v_a_437_, v_b_438_);
stack->m_num = v_res_451_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
uint8_t v_b_boxed_455_; uint8_t v_res_456_; lean_object* v_r_457_; 
v_b_boxed_455_ = lean_unbox(v_b_454_);
v_res_456_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_452_, v_a_453_, v_b_boxed_455_);
lean_dec_ref(v_s_452_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_458_){
_start:
{
lean_object* v_searcher_459_; uint8_t v___x_460_; uint8_t v___x_461_; 
v_searcher_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = 0;
v___x_461_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_458_, v_searcher_459_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_458_ = stack[0].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_458_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_463_);
lean_dec_ref(v_s_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_466_, lean_object* v_s_467_, uint8_t v_force_468_){
_start:
{
uint8_t v___y_479_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_startInclusive_483_; lean_object* v_endExclusive_484_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; uint32_t v___y_508_; uint32_t v___y_513_; uint32_t v___y_519_; 
if (v_escape_466_ == 0)
{
return v_s_467_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_string_utf8_byte_size(v_s_467_);
v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_539_ = lean_string_append(v___x_538_, v_s_467_);
lean_dec_ref(v_s_467_);
v___x_540_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
return v___x_541_;
}
else
{
if (v_force_468_ == 0)
{
uint8_t v_c_542_; uint8_t v___x_551_; uint8_t v___x_552_; 
v_c_542_ = lean_string_get_byte_fast(v_s_467_, v___x_535_);
v___x_551_ = 97;
v___x_552_ = lean_uint8_dec_le(v___x_551_, v_c_542_);
if (v___x_552_ == 0)
{
goto v___jp_546_;
}
else
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 122;
v___x_554_ = lean_uint8_dec_le(v_c_542_, v___x_553_);
if (v___x_554_ == 0)
{
goto v___jp_546_;
}
else
{
goto v___jp_532_;
}
}
v___jp_543_:
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 95;
v___x_545_ = lean_uint8_dec_eq(v_c_542_, v___x_544_);
if (v___x_545_ == 0)
{
goto v___jp_524_;
}
else
{
goto v___jp_532_;
}
}
v___jp_546_:
{
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 65;
v___x_548_ = lean_uint8_dec_le(v___x_547_, v_c_542_);
if (v___x_548_ == 0)
{
goto v___jp_543_;
}
else
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 90;
v___x_550_ = lean_uint8_dec_le(v_c_542_, v___x_549_);
if (v___x_550_ == 0)
{
goto v___jp_543_;
}
else
{
goto v___jp_532_;
}
}
}
}
else
{
goto v___jp_469_;
}
}
}
v___jp_469_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_string_utf8_byte_size(v_s_467_);
lean_inc_ref(v_s_467_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v_s_467_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
v___x_473_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_472_);
lean_dec_ref_known(v___x_472_, 3);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_475_ = lean_string_append(v___x_474_, v_s_467_);
lean_dec_ref(v_s_467_);
v___x_476_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
return v___x_477_;
}
else
{
return v_s_467_;
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
goto v___jp_469_;
}
else
{
return v_s_467_;
}
}
v___jp_480_:
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v_decide_487_; 
v___x_485_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_482_, v___y_481_);
lean_dec_ref(v___y_482_);
v___x_486_ = lean_nat_sub(v_endExclusive_484_, v_startInclusive_483_);
lean_dec(v_startInclusive_483_);
lean_dec(v_endExclusive_484_);
v_decide_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v___x_485_);
v___y_479_ = v_decide_487_;
goto v___jp_478_;
}
v___jp_488_:
{
if (v___y_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_startInclusive_495_; lean_object* v_endExclusive_496_; 
lean_dec(v___y_491_);
lean_dec(v___y_489_);
v___x_493_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_494_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_493_);
v_startInclusive_495_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_startInclusive_495_);
v_endExclusive_496_ = lean_ctor_get(v___x_494_, 2);
lean_inc(v_endExclusive_496_);
v___y_481_ = v___y_490_;
v___y_482_ = v___x_494_;
v_startInclusive_483_ = v_startInclusive_495_;
v_endExclusive_484_ = v_endExclusive_496_;
goto v___jp_480_;
}
else
{
lean_object* v___x_497_; 
lean_inc(v___y_491_);
lean_inc(v___y_489_);
lean_inc_ref(v_s_467_);
v___x_497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_497_, 0, v_s_467_);
lean_ctor_set(v___x_497_, 1, v___y_489_);
lean_ctor_set(v___x_497_, 2, v___y_491_);
v___y_481_ = v___y_490_;
v___y_482_ = v___x_497_;
v_startInclusive_483_ = v___y_489_;
v_endExclusive_484_ = v___y_491_;
goto v___jp_480_;
}
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_string_utf8_byte_size(v_s_467_);
lean_inc_ref(v_s_467_);
v___x_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_501_, 0, v_s_467_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
lean_ctor_set(v___x_501_, 2, v___x_500_);
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = l_Substring_Raw_nextn(v___x_501_, v___x_502_, v___x_499_);
lean_dec_ref_known(v___x_501_, 3);
v___x_504_ = lean_string_is_valid_pos(v_s_467_, v___x_503_);
if (v___x_504_ == 0)
{
v___y_489_ = v___x_503_;
v___y_490_ = v___x_499_;
v___y_491_ = v___x_500_;
v___y_492_ = v___x_504_;
goto v___jp_488_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = lean_string_is_valid_pos(v_s_467_, v___x_500_);
if (v___x_505_ == 0)
{
v___y_489_ = v___x_503_;
v___y_490_ = v___x_499_;
v___y_491_ = v___x_500_;
v___y_492_ = v___x_505_;
goto v___jp_488_;
}
else
{
uint8_t v___x_506_; 
v___x_506_ = lean_nat_dec_le(v___x_503_, v___x_500_);
v___y_489_ = v___x_503_;
v___y_490_ = v___x_499_;
v___y_491_ = v___x_500_;
v___y_492_ = v___x_506_;
goto v___jp_488_;
}
}
}
v___jp_507_:
{
uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = 95;
v___x_510_ = lean_uint32_dec_eq(v___y_508_, v___x_509_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_isLetterLike(v___y_508_);
if (v___x_511_ == 0)
{
v___y_479_ = v___x_511_;
goto v___jp_478_;
}
else
{
goto v___jp_498_;
}
}
else
{
goto v___jp_498_;
}
}
v___jp_512_:
{
uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = 97;
v___x_515_ = lean_uint32_dec_le(v___x_514_, v___y_513_);
if (v___x_515_ == 0)
{
v___y_508_ = v___y_513_;
goto v___jp_507_;
}
else
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 122;
v___x_517_ = lean_uint32_dec_le(v___y_513_, v___x_516_);
if (v___x_517_ == 0)
{
v___y_508_ = v___y_513_;
goto v___jp_507_;
}
else
{
goto v___jp_498_;
}
}
}
v___jp_518_:
{
uint32_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = 65;
v___x_521_ = lean_uint32_dec_le(v___x_520_, v___y_519_);
if (v___x_521_ == 0)
{
v___y_513_ = v___y_519_;
goto v___jp_512_;
}
else
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 90;
v___x_523_ = lean_uint32_dec_le(v___y_519_, v___x_522_);
if (v___x_523_ == 0)
{
v___y_513_ = v___y_519_;
goto v___jp_512_;
}
else
{
goto v___jp_498_;
}
}
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_string_utf8_byte_size(v_s_467_);
lean_inc_ref(v_s_467_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v_s_467_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
v___x_528_ = l_String_Slice_Pos_get_x3f(v___x_527_, v___x_525_);
lean_dec_ref_known(v___x_527_, 3);
if (lean_obj_tag(v___x_528_) == 0)
{
uint32_t v___x_529_; 
v___x_529_ = 65;
v___y_519_ = v___x_529_;
goto v___jp_518_;
}
else
{
lean_object* v_val_530_; uint32_t v___x_531_; 
v_val_530_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_528_, 1);
v___x_531_ = lean_unbox_uint32(v_val_530_);
lean_dec(v_val_530_);
v___y_519_ = v___x_531_;
goto v___jp_518_;
}
}
v___jp_532_:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_467_, v___x_533_);
if (v___x_534_ == 0)
{
goto v___jp_524_;
}
else
{
v___y_479_ = v___x_534_;
goto v___jp_478_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_0interp(lean_interpreter_value* stack)
{
uint8_t v_escape_466_ = stack[0].m_num;
lean_object* v_s_467_ = stack[1].m_obj;
uint8_t v_force_468_ = stack[2].m_num;
lean_object* v_res_555_;
v_res_555_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_466_, v_s_467_, v_force_468_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_556_, lean_object* v_s_557_, lean_object* v_force_558_){
_start:
{
uint8_t v_escape_boxed_559_; uint8_t v_force_boxed_560_; lean_object* v_res_561_; 
v_escape_boxed_559_ = lean_unbox(v_escape_556_);
v_force_boxed_560_ = lean_unbox(v_force_558_);
v_res_561_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_559_, v_s_557_, v_force_boxed_560_);
return v_res_561_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_562_, lean_object* v_inst_563_, lean_object* v_R_564_, lean_object* v_a_565_, uint8_t v_b_566_, lean_object* v_c_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_562_, v_a_565_, v_b_566_);
return v___x_568_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_562_ = stack[0].m_obj;
lean_object* v_a_565_ = stack[3].m_obj;
uint8_t v_b_566_ = stack[4].m_num;
uint8_t v_res_569_;
v_res_569_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_562_, lean_box(0), lean_box(0), v_a_565_, v_b_566_, lean_box(0));
stack->m_num = v_res_569_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_570_, lean_object* v_inst_571_, lean_object* v_R_572_, lean_object* v_a_573_, lean_object* v_b_574_, lean_object* v_c_575_){
_start:
{
uint8_t v_b_boxed_576_; uint8_t v_res_577_; lean_object* v_r_578_; 
v_b_boxed_576_ = lean_unbox(v_b_574_);
v_res_577_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_570_, v_inst_571_, v_R_572_, v_a_573_, v_b_boxed_576_, v_c_575_);
lean_dec_ref(v_s_570_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = 0;
return v___x_580_;
}
}
LEAN_EXPORT void l_Lean_Name_toStringWithSep___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_579_ = stack[0].m_obj;
uint8_t v_res_581_;
v_res_581_ = l_Lean_Name_toStringWithSep___lam__0(v_x_579_);
stack->m_num = v_res_581_;
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Lean_Name_toStringWithSep___lam__0(v_x_582_);
lean_dec_ref(v_x_582_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_587_, uint8_t v_escape_588_, lean_object* v_n_589_, lean_object* v_isToken_590_){
_start:
{
switch(lean_obj_tag(v_n_589_))
{
case 0:
{
lean_object* v___x_591_; 
lean_dec_ref(v_isToken_590_);
v___x_591_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_591_;
}
case 1:
{
lean_object* v_pre_592_; 
v_pre_592_ = lean_ctor_get(v_n_589_, 0);
if (lean_obj_tag(v_pre_592_) == 0)
{
lean_object* v_str_593_; lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; 
v_str_593_ = lean_ctor_get(v_n_589_, 1);
lean_inc_ref_n(v_str_593_, 2);
lean_dec_ref_known(v_n_589_, 2);
v___x_594_ = lean_apply_1(v_isToken_590_, v_str_593_);
v___x_595_ = lean_unbox(v___x_594_);
v___x_596_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_588_, v_str_593_, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v_str_597_; lean_object* v_r_598_; lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v_r_x27_602_; 
lean_inc(v_pre_592_);
v_str_597_ = lean_ctor_get(v_n_589_, 1);
lean_inc_ref_n(v_str_597_, 2);
lean_dec_ref_known(v_n_589_, 2);
lean_inc_ref(v_isToken_590_);
v_r_598_ = l_Lean_Name_toStringWithSep(v_sep_587_, v_escape_588_, v_pre_592_, v_isToken_590_);
v___x_599_ = lean_string_append(v_r_598_, v_sep_587_);
v___x_600_ = 0;
v___x_601_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_588_, v_str_597_, v___x_600_);
lean_inc_ref(v___x_599_);
v_r_x27_602_ = lean_string_append(v___x_599_, v___x_601_);
lean_dec_ref(v___x_601_);
if (v_escape_588_ == 0)
{
lean_dec_ref(v___x_599_);
lean_dec_ref(v_str_597_);
lean_dec_ref(v_isToken_590_);
return v_r_x27_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
lean_inc_ref(v_r_x27_602_);
v___x_603_ = lean_apply_1(v_isToken_590_, v_r_x27_602_);
v___x_604_ = lean_unbox(v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v___x_599_);
lean_dec_ref(v_str_597_);
return v_r_x27_602_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec_ref(v_r_x27_602_);
v___x_605_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_588_, v_str_597_, v_escape_588_);
v___x_606_ = lean_string_append(v___x_599_, v___x_605_);
lean_dec_ref(v___x_605_);
return v___x_606_;
}
}
}
}
default: 
{
lean_object* v_pre_607_; 
lean_dec_ref(v_isToken_590_);
v_pre_607_ = lean_ctor_get(v_n_589_, 0);
if (lean_obj_tag(v_pre_607_) == 0)
{
lean_object* v_i_608_; lean_object* v___x_609_; 
v_i_608_ = lean_ctor_get(v_n_589_, 1);
lean_inc(v_i_608_);
lean_dec_ref_known(v_n_589_, 2);
v___x_609_ = l_Nat_reprFast(v_i_608_);
return v___x_609_;
}
else
{
lean_object* v_i_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc(v_pre_607_);
v_i_610_ = lean_ctor_get(v_n_589_, 1);
lean_inc(v_i_610_);
lean_dec_ref_known(v_n_589_, 2);
v___f_611_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_612_ = l_Lean_Name_toStringWithSep(v_sep_587_, v_escape_588_, v_pre_607_, v___f_611_);
v___x_613_ = lean_string_append(v___x_612_, v_sep_587_);
v___x_614_ = l_Nat_reprFast(v_i_610_);
v___x_615_ = lean_string_append(v___x_613_, v___x_614_);
lean_dec_ref(v___x_614_);
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Name_toStringWithSep_0interp(lean_interpreter_value* stack)
{
lean_object* v_sep_587_ = stack[0].m_obj;
uint8_t v_escape_588_ = stack[1].m_num;
lean_object* v_n_589_ = stack[2].m_obj;
lean_object* v_isToken_590_ = stack[3].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Lean_Name_toStringWithSep(v_sep_587_, v_escape_588_, v_n_589_, v_isToken_590_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_617_, lean_object* v_escape_618_, lean_object* v_n_619_, lean_object* v_isToken_620_){
_start:
{
uint8_t v_escape_boxed_621_; lean_object* v_res_622_; 
v_escape_boxed_621_ = lean_unbox(v_escape_618_);
v_res_622_ = l_Lean_Name_toStringWithSep(v_sep_617_, v_escape_boxed_621_, v_n_619_, v_isToken_620_);
lean_dec_ref(v_sep_617_);
return v_res_622_;
}
}
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; uint8_t v___x_631_; 
v___x_629_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_630_ = lean_name_eq(v_n_628_, v___x_629_);
v___x_631_ = 1;
if (v___x_630_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Name_getRoot(v_n_628_);
if (lean_obj_tag(v___x_632_) == 1)
{
lean_object* v_str_633_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_str_633_ = lean_ctor_get(v___x_632_, 1);
lean_inc_ref(v_str_633_);
lean_dec_ref_known(v___x_632_, 2);
v___x_641_ = lean_string_utf8_byte_size(v_str_633_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_dec_le(v___x_642_, v___x_641_);
if (v___x_643_ == 0)
{
goto v___jp_634_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_string_memcmp(v_str_633_, v___x_644_, v___x_645_, v___x_645_, v___x_642_);
if (v___x_646_ == 0)
{
goto v___jp_634_;
}
else
{
lean_dec_ref(v_str_633_);
return v___x_631_;
}
}
v___jp_634_:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_string_utf8_byte_size(v_str_633_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_dec_le(v___x_636_, v___x_635_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_str_633_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_string_memcmp(v_str_633_, v___x_638_, v___x_639_, v___x_639_, v___x_636_);
lean_dec_ref(v_str_633_);
return v___x_640_;
}
}
}
else
{
lean_dec(v___x_632_);
return v___x_630_;
}
}
else
{
return v___x_631_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_628_ = stack[0].m_obj;
uint8_t v_res_647_;
v_res_647_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_628_);
stack->m_num = v_res_647_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_648_);
lean_dec(v_n_648_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_652_, uint8_t v_escape_653_, lean_object* v_isToken_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_653_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Name_toStringWithSep(v___x_655_, v_escape_653_, v_n_652_, v_isToken_654_);
return v___x_656_;
}
else
{
uint8_t v___x_657_; 
lean_inc(v_n_652_);
v___x_657_ = l_Lean_Name_isInaccessibleUserName(v_n_652_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_Name_hasMacroScopes(v_n_652_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_652_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Name_toStringWithSep(v___x_655_, v_escape_653_, v_n_652_, v_isToken_654_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Name_toStringWithSep(v___x_655_, v___x_658_, v_n_652_, v_isToken_654_);
return v___x_661_;
}
}
else
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Name_toStringWithSep(v___x_655_, v___x_657_, v_n_652_, v_isToken_654_);
return v___x_662_;
}
}
else
{
uint8_t v___x_663_; lean_object* v___x_664_; 
v___x_663_ = 0;
v___x_664_ = l_Lean_Name_toStringWithSep(v___x_655_, v___x_663_, v_n_652_, v_isToken_654_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_toStringWithToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_652_ = stack[0].m_obj;
uint8_t v_escape_653_ = stack[1].m_num;
lean_object* v_isToken_654_ = stack[2].m_obj;
lean_object* v_res_665_;
v_res_665_ = l_Lean_Name_toStringWithToken(v_n_652_, v_escape_653_, v_isToken_654_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_666_, lean_object* v_escape_667_, lean_object* v_isToken_668_){
_start:
{
uint8_t v_escape_boxed_669_; lean_object* v_res_670_; 
v_escape_boxed_669_ = lean_unbox(v_escape_667_);
v_res_670_ = l_Lean_Name_toStringWithToken(v_n_666_, v_escape_boxed_669_, v_isToken_668_);
return v_res_670_;
}
}
lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_671_, uint8_t v_escape_672_, lean_object* v_n_673_){
_start:
{
switch(lean_obj_tag(v_n_673_))
{
case 0:
{
lean_object* v___x_674_; 
v___x_674_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_674_;
}
case 1:
{
lean_object* v_pre_675_; 
v_pre_675_ = lean_ctor_get(v_n_673_, 0);
if (lean_obj_tag(v_pre_675_) == 0)
{
lean_object* v_str_676_; uint8_t v___x_677_; lean_object* v___x_678_; 
v_str_676_ = lean_ctor_get(v_n_673_, 1);
lean_inc_ref(v_str_676_);
lean_dec_ref_known(v_n_673_, 2);
v___x_677_ = 0;
v___x_678_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_672_, v_str_676_, v___x_677_);
return v___x_678_;
}
else
{
lean_object* v_str_679_; lean_object* v_r_680_; lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v_r_x27_684_; 
lean_inc(v_pre_675_);
v_str_679_ = lean_ctor_get(v_n_673_, 1);
lean_inc_ref(v_str_679_);
lean_dec_ref_known(v_n_673_, 2);
v_r_680_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_671_, v_escape_672_, v_pre_675_);
v___x_681_ = lean_string_append(v_r_680_, v_sep_671_);
v___x_682_ = 0;
v___x_683_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_672_, v_str_679_, v___x_682_);
v_r_x27_684_ = lean_string_append(v___x_681_, v___x_683_);
lean_dec_ref(v___x_683_);
return v_r_x27_684_;
}
}
default: 
{
lean_object* v_pre_685_; 
v_pre_685_ = lean_ctor_get(v_n_673_, 0);
if (lean_obj_tag(v_pre_685_) == 0)
{
lean_object* v_i_686_; lean_object* v___x_687_; 
v_i_686_ = lean_ctor_get(v_n_673_, 1);
lean_inc(v_i_686_);
lean_dec_ref_known(v_n_673_, 2);
v___x_687_ = l_Nat_reprFast(v_i_686_);
return v___x_687_;
}
else
{
lean_object* v_i_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_inc(v_pre_685_);
v_i_688_ = lean_ctor_get(v_n_673_, 1);
lean_inc(v_i_688_);
lean_dec_ref_known(v_n_673_, 2);
v___x_689_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_671_, v_escape_672_, v_pre_685_);
v___x_690_ = lean_string_append(v___x_689_, v_sep_671_);
v___x_691_ = l_Nat_reprFast(v_i_688_);
v___x_692_ = lean_string_append(v___x_690_, v___x_691_);
lean_dec_ref(v___x_691_);
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sep_671_ = stack[0].m_obj;
uint8_t v_escape_672_ = stack[1].m_num;
lean_object* v_n_673_ = stack[2].m_obj;
lean_object* v_res_693_;
v_res_693_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_671_, v_escape_672_, v_n_673_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_694_, lean_object* v_escape_695_, lean_object* v_n_696_){
_start:
{
uint8_t v_escape_boxed_697_; lean_object* v_res_698_; 
v_escape_boxed_697_ = lean_unbox(v_escape_695_);
v_res_698_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_694_, v_escape_boxed_697_, v_n_696_);
lean_dec_ref(v_sep_694_);
return v_res_698_;
}
}
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_699_, uint8_t v_escape_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_700_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_701_, v_escape_700_, v_n_699_);
return v___x_702_;
}
else
{
uint8_t v___x_703_; 
lean_inc(v_n_699_);
v___x_703_ = l_Lean_Name_isInaccessibleUserName(v_n_699_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Name_hasMacroScopes(v_n_699_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_699_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_701_, v_escape_700_, v_n_699_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_701_, v___x_704_, v_n_699_);
return v___x_707_;
}
}
else
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_701_, v___x_703_, v_n_699_);
return v___x_708_;
}
}
else
{
uint8_t v___x_709_; lean_object* v___x_710_; 
v___x_709_ = 0;
v___x_710_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_701_, v___x_709_, v_n_699_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT void l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_699_ = stack[0].m_obj;
uint8_t v_escape_700_ = stack[1].m_num;
lean_object* v_res_711_;
v_res_711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_699_, v_escape_700_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_712_, lean_object* v_escape_713_){
_start:
{
uint8_t v_escape_boxed_714_; lean_object* v_res_715_; 
v_escape_boxed_714_ = lean_unbox(v_escape_713_);
v_res_715_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_712_, v_escape_boxed_714_);
return v_res_715_;
}
}
lean_object* l_Lean_Name_toString(lean_object* v_n_716_, uint8_t v_escape_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_716_, v_escape_717_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Lean_Name_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_716_ = stack[0].m_obj;
uint8_t v_escape_717_ = stack[1].m_num;
lean_object* v_res_719_;
v_res_719_ = l_Lean_Name_toString(v_n_716_, v_escape_717_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_720_, lean_object* v_escape_721_){
_start:
{
uint8_t v_escape_boxed_722_; lean_object* v_res_723_; 
v_escape_boxed_722_ = lean_unbox(v_escape_721_);
v_res_723_ = l_Lean_Name_toString(v_n_720_, v_escape_boxed_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_724_){
_start:
{
uint8_t v___x_725_; lean_object* v___x_726_; 
v___x_725_ = 1;
v___x_726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_724_, v___x_725_);
return v___x_726_;
}
}
lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ToString_Name(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ToString_Name(builtin);
}
#ifdef __cplusplus
}
#endif
