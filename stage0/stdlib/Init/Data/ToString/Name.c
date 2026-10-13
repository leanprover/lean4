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
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_1_, lean_object* v_i_2_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_34_, lean_object* v_i_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_34_, v_i_35_);
lean_dec_ref(v_s_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_38_){
_start:
{
lean_object* v___x_42_; uint8_t v_c_43_; uint8_t v___x_52_; uint8_t v___x_53_; 
v___x_42_ = lean_unsigned_to_nat(0u);
v_c_43_ = lean_string_get_byte_fast(v_s_38_, v___x_42_);
v___x_52_ = 97;
v___x_53_ = lean_uint8_dec_le(v___x_52_, v_c_43_);
if (v___x_53_ == 0)
{
goto v___jp_47_;
}
else
{
uint8_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 122;
v___x_55_ = lean_uint8_dec_le(v_c_43_, v___x_54_);
if (v___x_55_ == 0)
{
goto v___jp_47_;
}
else
{
goto v___jp_39_;
}
}
v___jp_39_:
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_38_, v___x_40_);
return v___x_41_;
}
v___jp_44_:
{
uint8_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = 95;
v___x_46_ = lean_uint8_dec_eq(v_c_43_, v___x_45_);
if (v___x_46_ == 0)
{
return v___x_46_;
}
else
{
goto v___jp_39_;
}
}
v___jp_47_:
{
uint8_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = 65;
v___x_49_ = lean_uint8_dec_le(v___x_48_, v_c_43_);
if (v___x_49_ == 0)
{
goto v___jp_44_;
}
else
{
uint8_t v___x_50_; uint8_t v___x_51_; 
v___x_50_ = 90;
v___x_51_ = lean_uint8_dec_le(v_c_43_, v___x_50_);
if (v___x_51_ == 0)
{
goto v___jp_44_;
}
else
{
goto v___jp_39_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_56_);
lean_dec_ref(v_s_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_59_, lean_object* v_h_60_){
_start:
{
lean_object* v___x_64_; uint8_t v_c_65_; uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v_c_65_ = lean_string_get_byte_fast(v_s_59_, v___x_64_);
v___x_74_ = 97;
v___x_75_ = lean_uint8_dec_le(v___x_74_, v_c_65_);
if (v___x_75_ == 0)
{
goto v___jp_69_;
}
else
{
uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 122;
v___x_77_ = lean_uint8_dec_le(v_c_65_, v___x_76_);
if (v___x_77_ == 0)
{
goto v___jp_69_;
}
else
{
goto v___jp_61_;
}
}
v___jp_61_:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_59_, v___x_62_);
return v___x_63_;
}
v___jp_66_:
{
uint8_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 95;
v___x_68_ = lean_uint8_dec_eq(v_c_65_, v___x_67_);
if (v___x_68_ == 0)
{
return v___x_68_;
}
else
{
goto v___jp_61_;
}
}
v___jp_69_:
{
uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 65;
v___x_71_ = lean_uint8_dec_le(v___x_70_, v_c_65_);
if (v___x_71_ == 0)
{
goto v___jp_66_;
}
else
{
uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 90;
v___x_73_ = lean_uint8_dec_le(v_c_65_, v___x_72_);
if (v___x_73_ == 0)
{
goto v___jp_66_;
}
else
{
goto v___jp_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_78_, lean_object* v_h_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(v_s_78_, v_h_79_);
lean_dec_ref(v_s_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2));
v___x_86_ = lean_unsigned_to_nat(14u);
v___x_87_ = lean_unsigned_to_nat(22u);
v___x_88_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1));
v___x_89_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_90_ = l_mkPanicMessageWithDecl(v___x_89_, v___x_88_, v___x_87_, v___x_86_, v___x_85_);
return v___x_90_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_92_){
_start:
{
lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v_startInclusive_97_; lean_object* v_endExclusive_98_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; uint8_t v___y_109_; uint32_t v___y_127_; uint32_t v___y_132_; uint32_t v___y_138_; lean_object* v___x_154_; uint8_t v_c_155_; uint8_t v___x_164_; uint8_t v___x_165_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v_c_155_ = lean_string_get_byte_fast(v_s_92_, v___x_154_);
v___x_164_ = 97;
v___x_165_ = lean_uint8_dec_le(v___x_164_, v_c_155_);
if (v___x_165_ == 0)
{
goto v___jp_159_;
}
else
{
uint8_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 122;
v___x_167_ = lean_uint8_dec_le(v_c_155_, v___x_166_);
if (v___x_167_ == 0)
{
goto v___jp_159_;
}
else
{
goto v___jp_151_;
}
}
v___jp_93_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v_decide_102_; 
lean_inc_ref(v___y_95_);
v___x_99_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_95_);
v___x_100_ = l_String_Slice_Pos_skipWhile___redArg(v___y_96_, v___y_94_, v___x_99_);
lean_dec_ref(v___y_96_);
v___x_101_ = lean_nat_sub(v_endExclusive_98_, v_startInclusive_97_);
lean_dec(v_startInclusive_97_);
lean_dec(v_endExclusive_98_);
v_decide_102_ = lean_nat_dec_eq(v___x_100_, v___x_101_);
lean_dec(v___x_101_);
lean_dec(v___x_100_);
return v_decide_102_;
}
v___jp_103_:
{
if (v___y_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_startInclusive_112_; lean_object* v_endExclusive_113_; 
lean_dec(v___y_108_);
lean_dec(v___y_104_);
lean_dec_ref(v_s_92_);
v___x_110_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_111_ = l_panic___redArg(v___y_105_, v___x_110_);
v_startInclusive_112_ = lean_ctor_get(v___x_111_, 1);
lean_inc(v_startInclusive_112_);
v_endExclusive_113_ = lean_ctor_get(v___x_111_, 2);
lean_inc(v_endExclusive_113_);
v___y_94_ = v___y_106_;
v___y_95_ = v___y_107_;
v___y_96_ = v___x_111_;
v_startInclusive_97_ = v_startInclusive_112_;
v_endExclusive_98_ = v_endExclusive_113_;
goto v___jp_93_;
}
else
{
lean_object* v___x_114_; 
lean_inc(v___y_108_);
lean_inc(v___y_104_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v_s_92_);
lean_ctor_set(v___x_114_, 1, v___y_104_);
lean_ctor_set(v___x_114_, 2, v___y_108_);
v___y_94_ = v___y_106_;
v___y_95_ = v___y_107_;
v___y_96_ = v___x_114_;
v_startInclusive_97_ = v___y_104_;
v_endExclusive_98_ = v___y_108_;
goto v___jp_93_;
}
}
v___jp_115_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_string_utf8_byte_size(v_s_92_);
lean_inc_ref(v_s_92_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v_s_92_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = l_Substring_Raw_nextn(v___x_118_, v___x_119_, v___x_116_);
lean_dec_ref_known(v___x_118_, 3);
v___x_121_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_122_ = l_String_instInhabitedSlice;
v___x_123_ = lean_string_is_valid_pos(v_s_92_, v___x_120_);
if (v___x_123_ == 0)
{
v___y_104_ = v___x_120_;
v___y_105_ = v___x_122_;
v___y_106_ = v___x_116_;
v___y_107_ = v___x_121_;
v___y_108_ = v___x_117_;
v___y_109_ = v___x_123_;
goto v___jp_103_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = lean_string_is_valid_pos(v_s_92_, v___x_117_);
if (v___x_124_ == 0)
{
v___y_104_ = v___x_120_;
v___y_105_ = v___x_122_;
v___y_106_ = v___x_116_;
v___y_107_ = v___x_121_;
v___y_108_ = v___x_117_;
v___y_109_ = v___x_124_;
goto v___jp_103_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_le(v___x_120_, v___x_117_);
v___y_104_ = v___x_120_;
v___y_105_ = v___x_122_;
v___y_106_ = v___x_116_;
v___y_107_ = v___x_121_;
v___y_108_ = v___x_117_;
v___y_109_ = v___x_125_;
goto v___jp_103_;
}
}
}
v___jp_126_:
{
uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 95;
v___x_129_ = lean_uint32_dec_eq(v___y_127_, v___x_128_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
v___x_130_ = l_Lean_isLetterLike(v___y_127_);
if (v___x_130_ == 0)
{
lean_dec_ref(v_s_92_);
return v___x_130_;
}
else
{
goto v___jp_115_;
}
}
else
{
goto v___jp_115_;
}
}
v___jp_131_:
{
uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_133_ = 97;
v___x_134_ = lean_uint32_dec_le(v___x_133_, v___y_132_);
if (v___x_134_ == 0)
{
v___y_127_ = v___y_132_;
goto v___jp_126_;
}
else
{
uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_135_ = 122;
v___x_136_ = lean_uint32_dec_le(v___y_132_, v___x_135_);
if (v___x_136_ == 0)
{
v___y_127_ = v___y_132_;
goto v___jp_126_;
}
else
{
goto v___jp_115_;
}
}
}
v___jp_137_:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 65;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v___y_138_);
if (v___x_140_ == 0)
{
v___y_132_ = v___y_138_;
goto v___jp_131_;
}
else
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 90;
v___x_142_ = lean_uint32_dec_le(v___y_138_, v___x_141_);
if (v___x_142_ == 0)
{
v___y_132_ = v___y_138_;
goto v___jp_131_;
}
else
{
goto v___jp_115_;
}
}
}
v___jp_143_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_string_utf8_byte_size(v_s_92_);
lean_inc_ref(v_s_92_);
v___x_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_146_, 0, v_s_92_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
v___x_147_ = l_String_Slice_Pos_get_x3f(v___x_146_, v___x_144_);
lean_dec_ref_known(v___x_146_, 3);
if (lean_obj_tag(v___x_147_) == 0)
{
uint32_t v___x_148_; 
v___x_148_ = 65;
v___y_138_ = v___x_148_;
goto v___jp_137_;
}
else
{
lean_object* v_val_149_; uint32_t v___x_150_; 
v_val_149_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v___x_147_, 1);
v___x_150_ = lean_unbox_uint32(v_val_149_);
lean_dec(v_val_149_);
v___y_138_ = v___x_150_;
goto v___jp_137_;
}
}
v___jp_151_:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_92_, v___x_152_);
if (v___x_153_ == 0)
{
goto v___jp_143_;
}
else
{
lean_dec_ref(v_s_92_);
return v___x_153_;
}
}
v___jp_156_:
{
uint8_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 95;
v___x_158_ = lean_uint8_dec_eq(v_c_155_, v___x_157_);
if (v___x_158_ == 0)
{
goto v___jp_143_;
}
else
{
goto v___jp_151_;
}
}
v___jp_159_:
{
uint8_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 65;
v___x_161_ = lean_uint8_dec_le(v___x_160_, v_c_155_);
if (v___x_161_ == 0)
{
goto v___jp_156_;
}
else
{
uint8_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 90;
v___x_163_ = lean_uint8_dec_le(v_c_155_, v___x_162_);
if (v___x_163_ == 0)
{
goto v___jp_156_;
}
else
{
goto v___jp_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_171_, lean_object* v_h_172_){
_start:
{
lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v_startInclusive_177_; lean_object* v_endExclusive_178_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; uint8_t v___y_189_; uint32_t v___y_207_; uint32_t v___y_212_; uint32_t v___y_218_; lean_object* v___x_234_; uint8_t v_c_235_; uint8_t v___x_244_; uint8_t v___x_245_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v_c_235_ = lean_string_get_byte_fast(v_s_171_, v___x_234_);
v___x_244_ = 97;
v___x_245_ = lean_uint8_dec_le(v___x_244_, v_c_235_);
if (v___x_245_ == 0)
{
goto v___jp_239_;
}
else
{
uint8_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 122;
v___x_247_ = lean_uint8_dec_le(v_c_235_, v___x_246_);
if (v___x_247_ == 0)
{
goto v___jp_239_;
}
else
{
goto v___jp_231_;
}
}
v___jp_173_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v_decide_182_; 
lean_inc_ref(v___y_175_);
v___x_179_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_175_);
v___x_180_ = l_String_Slice_Pos_skipWhile___redArg(v___y_176_, v___y_174_, v___x_179_);
lean_dec_ref(v___y_176_);
v___x_181_ = lean_nat_sub(v_endExclusive_178_, v_startInclusive_177_);
lean_dec(v_startInclusive_177_);
lean_dec(v_endExclusive_178_);
v_decide_182_ = lean_nat_dec_eq(v___x_180_, v___x_181_);
lean_dec(v___x_181_);
lean_dec(v___x_180_);
return v_decide_182_;
}
v___jp_183_:
{
if (v___y_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_startInclusive_192_; lean_object* v_endExclusive_193_; 
lean_dec(v___y_188_);
lean_dec(v___y_184_);
lean_dec_ref(v_s_171_);
v___x_190_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_191_ = l_panic___redArg(v___y_185_, v___x_190_);
v_startInclusive_192_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_startInclusive_192_);
v_endExclusive_193_ = lean_ctor_get(v___x_191_, 2);
lean_inc(v_endExclusive_193_);
v___y_174_ = v___y_186_;
v___y_175_ = v___y_187_;
v___y_176_ = v___x_191_;
v_startInclusive_177_ = v_startInclusive_192_;
v_endExclusive_178_ = v_endExclusive_193_;
goto v___jp_173_;
}
else
{
lean_object* v___x_194_; 
lean_inc(v___y_188_);
lean_inc(v___y_184_);
v___x_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_194_, 0, v_s_171_);
lean_ctor_set(v___x_194_, 1, v___y_184_);
lean_ctor_set(v___x_194_, 2, v___y_188_);
v___y_174_ = v___y_186_;
v___y_175_ = v___y_187_;
v___y_176_ = v___x_194_;
v_startInclusive_177_ = v___y_184_;
v_endExclusive_178_ = v___y_188_;
goto v___jp_173_;
}
}
v___jp_195_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_string_utf8_byte_size(v_s_171_);
lean_inc_ref(v_s_171_);
v___x_198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_198_, 0, v_s_171_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_197_);
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = l_Substring_Raw_nextn(v___x_198_, v___x_199_, v___x_196_);
lean_dec_ref_known(v___x_198_, 3);
v___x_201_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_202_ = l_String_instInhabitedSlice;
v___x_203_ = lean_string_is_valid_pos(v_s_171_, v___x_200_);
if (v___x_203_ == 0)
{
v___y_184_ = v___x_200_;
v___y_185_ = v___x_202_;
v___y_186_ = v___x_196_;
v___y_187_ = v___x_201_;
v___y_188_ = v___x_197_;
v___y_189_ = v___x_203_;
goto v___jp_183_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = lean_string_is_valid_pos(v_s_171_, v___x_197_);
if (v___x_204_ == 0)
{
v___y_184_ = v___x_200_;
v___y_185_ = v___x_202_;
v___y_186_ = v___x_196_;
v___y_187_ = v___x_201_;
v___y_188_ = v___x_197_;
v___y_189_ = v___x_204_;
goto v___jp_183_;
}
else
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_le(v___x_200_, v___x_197_);
v___y_184_ = v___x_200_;
v___y_185_ = v___x_202_;
v___y_186_ = v___x_196_;
v___y_187_ = v___x_201_;
v___y_188_ = v___x_197_;
v___y_189_ = v___x_205_;
goto v___jp_183_;
}
}
}
v___jp_206_:
{
uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = 95;
v___x_209_ = lean_uint32_dec_eq(v___y_207_, v___x_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = l_Lean_isLetterLike(v___y_207_);
if (v___x_210_ == 0)
{
lean_dec_ref(v_s_171_);
return v___x_210_;
}
else
{
goto v___jp_195_;
}
}
else
{
goto v___jp_195_;
}
}
v___jp_211_:
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 97;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v___y_212_);
if (v___x_214_ == 0)
{
v___y_207_ = v___y_212_;
goto v___jp_206_;
}
else
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 122;
v___x_216_ = lean_uint32_dec_le(v___y_212_, v___x_215_);
if (v___x_216_ == 0)
{
v___y_207_ = v___y_212_;
goto v___jp_206_;
}
else
{
goto v___jp_195_;
}
}
}
v___jp_217_:
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 65;
v___x_220_ = lean_uint32_dec_le(v___x_219_, v___y_218_);
if (v___x_220_ == 0)
{
v___y_212_ = v___y_218_;
goto v___jp_211_;
}
else
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 90;
v___x_222_ = lean_uint32_dec_le(v___y_218_, v___x_221_);
if (v___x_222_ == 0)
{
v___y_212_ = v___y_218_;
goto v___jp_211_;
}
else
{
goto v___jp_195_;
}
}
}
v___jp_223_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_string_utf8_byte_size(v_s_171_);
lean_inc_ref(v_s_171_);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v_s_171_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
v___x_227_ = l_String_Slice_Pos_get_x3f(v___x_226_, v___x_224_);
lean_dec_ref_known(v___x_226_, 3);
if (lean_obj_tag(v___x_227_) == 0)
{
uint32_t v___x_228_; 
v___x_228_ = 65;
v___y_218_ = v___x_228_;
goto v___jp_217_;
}
else
{
lean_object* v_val_229_; uint32_t v___x_230_; 
v_val_229_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_227_, 1);
v___x_230_ = lean_unbox_uint32(v_val_229_);
lean_dec(v_val_229_);
v___y_218_ = v___x_230_;
goto v___jp_217_;
}
}
v___jp_231_:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_171_, v___x_232_);
if (v___x_233_ == 0)
{
goto v___jp_223_;
}
else
{
lean_dec_ref(v_s_171_);
return v___x_233_;
}
}
v___jp_236_:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 95;
v___x_238_ = lean_uint8_dec_eq(v_c_235_, v___x_237_);
if (v___x_238_ == 0)
{
goto v___jp_223_;
}
else
{
goto v___jp_231_;
}
}
v___jp_239_:
{
uint8_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 65;
v___x_241_ = lean_uint8_dec_le(v___x_240_, v_c_235_);
if (v___x_241_ == 0)
{
goto v___jp_236_;
}
else
{
uint8_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 90;
v___x_243_ = lean_uint8_dec_le(v_c_235_, v___x_242_);
if (v___x_243_ == 0)
{
goto v___jp_236_;
}
else
{
goto v___jp_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_248_, lean_object* v_h_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_248_, v_h_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = l_Lean_idBeginEscape;
v___x_254_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_255_ = lean_string_push(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = l_Lean_idEndEscape;
v___x_257_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_258_ = lean_string_push(v___x_257_, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_261_ = lean_string_append(v___x_260_, v_s_259_);
v___x_262_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_263_ = lean_string_append(v___x_261_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_264_);
lean_dec_ref(v_s_264_);
return v_res_265_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_268_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_277_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_269_, v___x_276_, v___y_270_, lean_box(0), lean_box(0), v___y_273_, v___y_274_, v___y_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_281_, uint8_t v_force_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_string_utf8_byte_size(v_s_281_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_286_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_287_ = lean_string_append(v___x_286_, v_s_281_);
lean_dec_ref(v_s_281_);
v___x_288_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___f_291_; uint8_t v___y_303_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v_startInclusive_309_; lean_object* v_endExclusive_310_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; uint8_t v___y_321_; uint32_t v___y_337_; uint32_t v___y_342_; uint32_t v___y_348_; 
v___f_291_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_282_ == 0)
{
uint8_t v_c_362_; uint8_t v___x_371_; uint8_t v___x_372_; 
v_c_362_ = lean_string_get_byte_fast(v_s_281_, v___x_283_);
v___x_371_ = 97;
v___x_372_ = lean_uint8_dec_le(v___x_371_, v_c_362_);
if (v___x_372_ == 0)
{
goto v___jp_366_;
}
else
{
uint8_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 122;
v___x_374_ = lean_uint8_dec_le(v_c_362_, v___x_373_);
if (v___x_374_ == 0)
{
goto v___jp_366_;
}
else
{
goto v___jp_359_;
}
}
v___jp_363_:
{
uint8_t v___x_364_; uint8_t v___x_365_; 
v___x_364_ = 95;
v___x_365_ = lean_uint8_dec_eq(v_c_362_, v___x_364_);
if (v___x_365_ == 0)
{
goto v___jp_353_;
}
else
{
goto v___jp_359_;
}
}
v___jp_366_:
{
uint8_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 65;
v___x_368_ = lean_uint8_dec_le(v___x_367_, v_c_362_);
if (v___x_368_ == 0)
{
goto v___jp_363_;
}
else
{
uint8_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 90;
v___x_370_ = lean_uint8_dec_le(v_c_362_, v___x_369_);
if (v___x_370_ == 0)
{
goto v___jp_363_;
}
else
{
goto v___jp_359_;
}
}
}
}
else
{
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_281_);
v___x_294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_294_, 0, v_s_281_);
lean_ctor_set(v___x_294_, 1, v___x_283_);
lean_ctor_set(v___x_294_, 2, v___x_284_);
v___x_295_ = l_String_Slice_contains___redArg(v___f_291_, v___x_294_, v___x_293_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_296_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_297_ = lean_string_append(v___x_296_, v_s_281_);
lean_dec_ref(v_s_281_);
v___x_298_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
lean_dec_ref(v_s_281_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
v___jp_302_:
{
if (v___y_303_ == 0)
{
goto v___jp_292_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_s_281_);
return v___x_304_;
}
}
v___jp_305_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v_decide_314_; 
lean_inc_ref(v___y_307_);
v___x_311_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_307_);
v___x_312_ = l_String_Slice_Pos_skipWhile___redArg(v___y_308_, v___y_306_, v___x_311_);
lean_dec_ref(v___y_308_);
v___x_313_ = lean_nat_sub(v_endExclusive_310_, v_startInclusive_309_);
lean_dec(v_startInclusive_309_);
lean_dec(v_endExclusive_310_);
v_decide_314_ = lean_nat_dec_eq(v___x_312_, v___x_313_);
lean_dec(v___x_313_);
lean_dec(v___x_312_);
v___y_303_ = v_decide_314_;
goto v___jp_302_;
}
v___jp_315_:
{
if (v___y_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_startInclusive_324_; lean_object* v_endExclusive_325_; 
lean_dec(v___y_320_);
lean_dec(v___y_316_);
v___x_322_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_323_ = l_panic___redArg(v___y_319_, v___x_322_);
v_startInclusive_324_ = lean_ctor_get(v___x_323_, 1);
lean_inc(v_startInclusive_324_);
v_endExclusive_325_ = lean_ctor_get(v___x_323_, 2);
lean_inc(v_endExclusive_325_);
v___y_306_ = v___y_317_;
v___y_307_ = v___y_318_;
v___y_308_ = v___x_323_;
v_startInclusive_309_ = v_startInclusive_324_;
v_endExclusive_310_ = v_endExclusive_325_;
goto v___jp_305_;
}
else
{
lean_object* v___x_326_; 
lean_inc(v___y_320_);
lean_inc(v___y_316_);
lean_inc_ref(v_s_281_);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v_s_281_);
lean_ctor_set(v___x_326_, 1, v___y_316_);
lean_ctor_set(v___x_326_, 2, v___y_320_);
v___y_306_ = v___y_317_;
v___y_307_ = v___y_318_;
v___y_308_ = v___x_326_;
v_startInclusive_309_ = v___y_316_;
v_endExclusive_310_ = v___y_320_;
goto v___jp_305_;
}
}
v___jp_327_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
lean_inc_ref(v_s_281_);
v___x_328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_328_, 0, v_s_281_);
lean_ctor_set(v___x_328_, 1, v___x_283_);
lean_ctor_set(v___x_328_, 2, v___x_284_);
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = l_Substring_Raw_nextn(v___x_328_, v___x_329_, v___x_283_);
lean_dec_ref_known(v___x_328_, 3);
v___x_331_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_332_ = l_String_instInhabitedSlice;
v___x_333_ = lean_string_is_valid_pos(v_s_281_, v___x_330_);
if (v___x_333_ == 0)
{
v___y_316_ = v___x_330_;
v___y_317_ = v___x_283_;
v___y_318_ = v___x_331_;
v___y_319_ = v___x_332_;
v___y_320_ = v___x_284_;
v___y_321_ = v___x_333_;
goto v___jp_315_;
}
else
{
uint8_t v___x_334_; 
v___x_334_ = lean_string_is_valid_pos(v_s_281_, v___x_284_);
if (v___x_334_ == 0)
{
v___y_316_ = v___x_330_;
v___y_317_ = v___x_283_;
v___y_318_ = v___x_331_;
v___y_319_ = v___x_332_;
v___y_320_ = v___x_284_;
v___y_321_ = v___x_334_;
goto v___jp_315_;
}
else
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_le(v___x_330_, v___x_284_);
v___y_316_ = v___x_330_;
v___y_317_ = v___x_283_;
v___y_318_ = v___x_331_;
v___y_319_ = v___x_332_;
v___y_320_ = v___x_284_;
v___y_321_ = v___x_335_;
goto v___jp_315_;
}
}
}
v___jp_336_:
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 95;
v___x_339_ = lean_uint32_dec_eq(v___y_337_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_isLetterLike(v___y_337_);
if (v___x_340_ == 0)
{
v___y_303_ = v___x_340_;
goto v___jp_302_;
}
else
{
goto v___jp_327_;
}
}
else
{
goto v___jp_327_;
}
}
v___jp_341_:
{
uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 97;
v___x_344_ = lean_uint32_dec_le(v___x_343_, v___y_342_);
if (v___x_344_ == 0)
{
v___y_337_ = v___y_342_;
goto v___jp_336_;
}
else
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 122;
v___x_346_ = lean_uint32_dec_le(v___y_342_, v___x_345_);
if (v___x_346_ == 0)
{
v___y_337_ = v___y_342_;
goto v___jp_336_;
}
else
{
goto v___jp_327_;
}
}
}
v___jp_347_:
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 65;
v___x_350_ = lean_uint32_dec_le(v___x_349_, v___y_348_);
if (v___x_350_ == 0)
{
v___y_342_ = v___y_348_;
goto v___jp_341_;
}
else
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 90;
v___x_352_ = lean_uint32_dec_le(v___y_348_, v___x_351_);
if (v___x_352_ == 0)
{
v___y_342_ = v___y_348_;
goto v___jp_341_;
}
else
{
goto v___jp_327_;
}
}
}
v___jp_353_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_inc_ref(v_s_281_);
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v_s_281_);
lean_ctor_set(v___x_354_, 1, v___x_283_);
lean_ctor_set(v___x_354_, 2, v___x_284_);
v___x_355_ = l_String_Slice_Pos_get_x3f(v___x_354_, v___x_283_);
lean_dec_ref_known(v___x_354_, 3);
if (lean_obj_tag(v___x_355_) == 0)
{
uint32_t v___x_356_; 
v___x_356_ = 65;
v___y_348_ = v___x_356_;
goto v___jp_347_;
}
else
{
lean_object* v_val_357_; uint32_t v___x_358_; 
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_355_, 1);
v___x_358_ = lean_unbox_uint32(v_val_357_);
lean_dec(v_val_357_);
v___y_348_ = v___x_358_;
goto v___jp_347_;
}
}
v___jp_359_:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_281_, v___x_360_);
if (v___x_361_ == 0)
{
goto v___jp_353_;
}
else
{
v___y_303_ = v___x_361_;
goto v___jp_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_375_, lean_object* v_force_376_){
_start:
{
uint8_t v_force_boxed_377_; lean_object* v_res_378_; 
v_force_boxed_377_ = lean_unbox(v_force_376_);
v_res_378_ = l_Lean_Name_escapePart(v_s_375_, v_force_boxed_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = l_String_instInhabitedSlice;
v___x_381_ = lean_panic_fn_borrowed(v___x_380_, v_msg_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_382_, lean_object* v_pos_383_){
_start:
{
lean_object* v_str_384_; lean_object* v_startInclusive_385_; lean_object* v_endExclusive_386_; lean_object* v___x_387_; uint8_t v___y_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v_decide_400_; 
v_str_384_ = lean_ctor_get(v_s_382_, 0);
v_startInclusive_385_ = lean_ctor_get(v_s_382_, 1);
v_endExclusive_386_ = lean_ctor_get(v_s_382_, 2);
v___x_387_ = lean_nat_add(v_startInclusive_385_, v_pos_383_);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_nat_sub(v_endExclusive_386_, v___x_387_);
v_decide_400_ = lean_nat_dec_eq(v___x_398_, v___x_399_);
lean_dec(v___x_399_);
if (v_decide_400_ == 0)
{
uint32_t v___x_401_; uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_401_ = lean_string_utf8_get_fast(v_str_384_, v___x_387_);
v___x_423_ = 65;
v___x_424_ = lean_uint32_dec_le(v___x_423_, v___x_401_);
if (v___x_424_ == 0)
{
goto v___jp_418_;
}
else
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 90;
v___x_426_ = lean_uint32_dec_le(v___x_401_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_418_;
}
else
{
goto v___jp_388_;
}
}
v___jp_402_:
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 95;
v___x_404_ = lean_uint32_dec_eq(v___x_401_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 39;
v___x_406_ = lean_uint32_dec_eq(v___x_401_, v___x_405_);
if (v___x_406_ == 0)
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 33;
v___x_408_ = lean_uint32_dec_eq(v___x_401_, v___x_407_);
if (v___x_408_ == 0)
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 63;
v___x_410_ = lean_uint32_dec_eq(v___x_401_, v___x_409_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_isLetterLike(v___x_401_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
v___x_412_ = l_Lean_isSubScriptAlnum(v___x_401_);
v___y_397_ = v___x_412_;
goto v___jp_396_;
}
else
{
v___y_397_ = v___x_411_;
goto v___jp_396_;
}
}
else
{
goto v___jp_388_;
}
}
else
{
goto v___jp_388_;
}
}
else
{
goto v___jp_388_;
}
}
else
{
goto v___jp_388_;
}
}
v___jp_413_:
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 48;
v___x_415_ = lean_uint32_dec_le(v___x_414_, v___x_401_);
if (v___x_415_ == 0)
{
goto v___jp_402_;
}
else
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 57;
v___x_417_ = lean_uint32_dec_le(v___x_401_, v___x_416_);
if (v___x_417_ == 0)
{
goto v___jp_402_;
}
else
{
goto v___jp_388_;
}
}
}
v___jp_418_:
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 97;
v___x_420_ = lean_uint32_dec_le(v___x_419_, v___x_401_);
if (v___x_420_ == 0)
{
goto v___jp_413_;
}
else
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 122;
v___x_422_ = lean_uint32_dec_le(v___x_401_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_413_;
}
else
{
goto v___jp_388_;
}
}
}
}
else
{
lean_dec(v___x_387_);
return v_pos_383_;
}
v___jp_388_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_389_ = lean_string_utf8_next_fast(v_str_384_, v___x_387_);
v___x_390_ = lean_nat_sub(v___x_389_, v___x_387_);
lean_dec(v___x_387_);
v___x_391_ = lean_nat_add(v_pos_383_, v___x_390_);
lean_dec(v___x_390_);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_add(v_pos_383_, v___x_392_);
v___x_394_ = lean_nat_dec_le(v___x_393_, v___x_391_);
lean_dec(v___x_393_);
if (v___x_394_ == 0)
{
lean_dec(v___x_391_);
return v_pos_383_;
}
else
{
lean_dec(v_pos_383_);
v_pos_383_ = v___x_391_;
goto _start;
}
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
lean_dec(v___x_387_);
return v_pos_383_;
}
else
{
goto v___jp_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_427_, lean_object* v_pos_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_427_, v_pos_428_);
lean_dec_ref(v_s_427_);
return v_res_429_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_430_, lean_object* v_a_431_, uint8_t v_b_432_){
_start:
{
lean_object* v_str_433_; lean_object* v_startInclusive_434_; lean_object* v_endExclusive_435_; lean_object* v___x_436_; uint8_t v_decide_437_; 
v_str_433_ = lean_ctor_get(v_s_430_, 0);
v_startInclusive_434_ = lean_ctor_get(v_s_430_, 1);
v_endExclusive_435_ = lean_ctor_get(v_s_430_, 2);
v___x_436_ = lean_nat_sub(v_endExclusive_435_, v_startInclusive_434_);
v_decide_437_ = lean_nat_dec_eq(v_a_431_, v___x_436_);
lean_dec(v___x_436_);
if (v_decide_437_ == 0)
{
lean_object* v___x_438_; uint32_t v___x_439_; uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_438_ = lean_nat_add(v_startInclusive_434_, v_a_431_);
lean_dec(v_a_431_);
v___x_439_ = lean_string_utf8_get_fast(v_str_433_, v___x_438_);
v___x_440_ = l_Lean_idEndEscape;
v___x_441_ = lean_uint32_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_string_utf8_next_fast(v_str_433_, v___x_438_);
lean_dec(v___x_438_);
v___x_443_ = lean_nat_sub(v___x_442_, v_startInclusive_434_);
v_a_431_ = v___x_443_;
v_b_432_ = v___x_441_;
goto _start;
}
else
{
lean_dec(v___x_438_);
return v___x_441_;
}
}
else
{
lean_dec(v_a_431_);
return v_b_432_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
uint8_t v_b_boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v_b_boxed_448_ = lean_unbox(v_b_447_);
v_res_449_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_445_, v_a_446_, v_b_boxed_448_);
lean_dec_ref(v_s_445_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_451_){
_start:
{
lean_object* v_searcher_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
v_searcher_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = 0;
v___x_454_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_451_, v_searcher_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_455_);
lean_dec_ref(v_s_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_458_, lean_object* v_s_459_, uint8_t v_force_460_){
_start:
{
uint8_t v___y_471_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v_startInclusive_475_; lean_object* v_endExclusive_476_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; uint32_t v___y_500_; uint32_t v___y_505_; uint32_t v___y_511_; 
if (v_escape_458_ == 0)
{
return v_s_459_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_string_utf8_byte_size(v_s_459_);
v___x_529_ = lean_nat_dec_lt(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_531_ = lean_string_append(v___x_530_, v_s_459_);
lean_dec_ref(v_s_459_);
v___x_532_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_533_ = lean_string_append(v___x_531_, v___x_532_);
return v___x_533_;
}
else
{
if (v_force_460_ == 0)
{
uint8_t v_c_534_; uint8_t v___x_543_; uint8_t v___x_544_; 
v_c_534_ = lean_string_get_byte_fast(v_s_459_, v___x_527_);
v___x_543_ = 97;
v___x_544_ = lean_uint8_dec_le(v___x_543_, v_c_534_);
if (v___x_544_ == 0)
{
goto v___jp_538_;
}
else
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = 122;
v___x_546_ = lean_uint8_dec_le(v_c_534_, v___x_545_);
if (v___x_546_ == 0)
{
goto v___jp_538_;
}
else
{
goto v___jp_524_;
}
}
v___jp_535_:
{
uint8_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 95;
v___x_537_ = lean_uint8_dec_eq(v_c_534_, v___x_536_);
if (v___x_537_ == 0)
{
goto v___jp_516_;
}
else
{
goto v___jp_524_;
}
}
v___jp_538_:
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 65;
v___x_540_ = lean_uint8_dec_le(v___x_539_, v_c_534_);
if (v___x_540_ == 0)
{
goto v___jp_535_;
}
else
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = 90;
v___x_542_ = lean_uint8_dec_le(v_c_534_, v___x_541_);
if (v___x_542_ == 0)
{
goto v___jp_535_;
}
else
{
goto v___jp_524_;
}
}
}
}
else
{
goto v___jp_461_;
}
}
}
v___jp_461_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_string_utf8_byte_size(v_s_459_);
lean_inc_ref(v_s_459_);
v___x_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_464_, 0, v_s_459_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
v___x_465_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_464_);
lean_dec_ref_known(v___x_464_, 3);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_467_ = lean_string_append(v___x_466_, v_s_459_);
lean_dec_ref(v_s_459_);
v___x_468_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
return v___x_469_;
}
else
{
return v_s_459_;
}
}
v___jp_470_:
{
if (v___y_471_ == 0)
{
goto v___jp_461_;
}
else
{
return v_s_459_;
}
}
v___jp_472_:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v_decide_479_; 
v___x_477_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_474_, v___y_473_);
lean_dec_ref(v___y_474_);
v___x_478_ = lean_nat_sub(v_endExclusive_476_, v_startInclusive_475_);
lean_dec(v_startInclusive_475_);
lean_dec(v_endExclusive_476_);
v_decide_479_ = lean_nat_dec_eq(v___x_477_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_477_);
v___y_471_ = v_decide_479_;
goto v___jp_470_;
}
v___jp_480_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_startInclusive_487_; lean_object* v_endExclusive_488_; 
lean_dec(v___y_482_);
lean_dec(v___y_481_);
v___x_485_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_486_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_485_);
v_startInclusive_487_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_startInclusive_487_);
v_endExclusive_488_ = lean_ctor_get(v___x_486_, 2);
lean_inc(v_endExclusive_488_);
v___y_473_ = v___y_483_;
v___y_474_ = v___x_486_;
v_startInclusive_475_ = v_startInclusive_487_;
v_endExclusive_476_ = v_endExclusive_488_;
goto v___jp_472_;
}
else
{
lean_object* v___x_489_; 
lean_inc(v___y_482_);
lean_inc(v___y_481_);
lean_inc_ref(v_s_459_);
v___x_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_489_, 0, v_s_459_);
lean_ctor_set(v___x_489_, 1, v___y_481_);
lean_ctor_set(v___x_489_, 2, v___y_482_);
v___y_473_ = v___y_483_;
v___y_474_ = v___x_489_;
v_startInclusive_475_ = v___y_481_;
v_endExclusive_476_ = v___y_482_;
goto v___jp_472_;
}
}
v___jp_490_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_string_utf8_byte_size(v_s_459_);
lean_inc_ref(v_s_459_);
v___x_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_493_, 0, v_s_459_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
lean_ctor_set(v___x_493_, 2, v___x_492_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Substring_Raw_nextn(v___x_493_, v___x_494_, v___x_491_);
lean_dec_ref_known(v___x_493_, 3);
v___x_496_ = lean_string_is_valid_pos(v_s_459_, v___x_495_);
if (v___x_496_ == 0)
{
v___y_481_ = v___x_495_;
v___y_482_ = v___x_492_;
v___y_483_ = v___x_491_;
v___y_484_ = v___x_496_;
goto v___jp_480_;
}
else
{
uint8_t v___x_497_; 
v___x_497_ = lean_string_is_valid_pos(v_s_459_, v___x_492_);
if (v___x_497_ == 0)
{
v___y_481_ = v___x_495_;
v___y_482_ = v___x_492_;
v___y_483_ = v___x_491_;
v___y_484_ = v___x_497_;
goto v___jp_480_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = lean_nat_dec_le(v___x_495_, v___x_492_);
v___y_481_ = v___x_495_;
v___y_482_ = v___x_492_;
v___y_483_ = v___x_491_;
v___y_484_ = v___x_498_;
goto v___jp_480_;
}
}
}
v___jp_499_:
{
uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 95;
v___x_502_ = lean_uint32_dec_eq(v___y_500_, v___x_501_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
v___x_503_ = l_Lean_isLetterLike(v___y_500_);
if (v___x_503_ == 0)
{
v___y_471_ = v___x_503_;
goto v___jp_470_;
}
else
{
goto v___jp_490_;
}
}
else
{
goto v___jp_490_;
}
}
v___jp_504_:
{
uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = 97;
v___x_507_ = lean_uint32_dec_le(v___x_506_, v___y_505_);
if (v___x_507_ == 0)
{
v___y_500_ = v___y_505_;
goto v___jp_499_;
}
else
{
uint32_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = 122;
v___x_509_ = lean_uint32_dec_le(v___y_505_, v___x_508_);
if (v___x_509_ == 0)
{
v___y_500_ = v___y_505_;
goto v___jp_499_;
}
else
{
goto v___jp_490_;
}
}
}
v___jp_510_:
{
uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = 65;
v___x_513_ = lean_uint32_dec_le(v___x_512_, v___y_511_);
if (v___x_513_ == 0)
{
v___y_505_ = v___y_511_;
goto v___jp_504_;
}
else
{
uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = 90;
v___x_515_ = lean_uint32_dec_le(v___y_511_, v___x_514_);
if (v___x_515_ == 0)
{
v___y_505_ = v___y_511_;
goto v___jp_504_;
}
else
{
goto v___jp_490_;
}
}
}
v___jp_516_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_string_utf8_byte_size(v_s_459_);
lean_inc_ref(v_s_459_);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v_s_459_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
v___x_520_ = l_String_Slice_Pos_get_x3f(v___x_519_, v___x_517_);
lean_dec_ref_known(v___x_519_, 3);
if (lean_obj_tag(v___x_520_) == 0)
{
uint32_t v___x_521_; 
v___x_521_ = 65;
v___y_511_ = v___x_521_;
goto v___jp_510_;
}
else
{
lean_object* v_val_522_; uint32_t v___x_523_; 
v_val_522_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v___x_520_, 1);
v___x_523_ = lean_unbox_uint32(v_val_522_);
lean_dec(v_val_522_);
v___y_511_ = v___x_523_;
goto v___jp_510_;
}
}
v___jp_524_:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_459_, v___x_525_);
if (v___x_526_ == 0)
{
goto v___jp_516_;
}
else
{
v___y_471_ = v___x_526_;
goto v___jp_470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_547_, lean_object* v_s_548_, lean_object* v_force_549_){
_start:
{
uint8_t v_escape_boxed_550_; uint8_t v_force_boxed_551_; lean_object* v_res_552_; 
v_escape_boxed_550_ = lean_unbox(v_escape_547_);
v_force_boxed_551_ = lean_unbox(v_force_549_);
v_res_552_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_550_, v_s_548_, v_force_boxed_551_);
return v_res_552_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_553_, lean_object* v_inst_554_, lean_object* v_R_555_, lean_object* v_a_556_, uint8_t v_b_557_, lean_object* v_c_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_553_, v_a_556_, v_b_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_560_, lean_object* v_inst_561_, lean_object* v_R_562_, lean_object* v_a_563_, lean_object* v_b_564_, lean_object* v_c_565_){
_start:
{
uint8_t v_b_boxed_566_; uint8_t v_res_567_; lean_object* v_r_568_; 
v_b_boxed_566_ = lean_unbox(v_b_564_);
v_res_567_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_560_, v_inst_561_, v_R_562_, v_a_563_, v_b_boxed_566_, v_c_565_);
lean_dec_ref(v_s_560_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = 0;
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_Name_toStringWithSep___lam__0(v_x_571_);
lean_dec_ref(v_x_571_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_576_, uint8_t v_escape_577_, lean_object* v_n_578_, lean_object* v_isToken_579_){
_start:
{
switch(lean_obj_tag(v_n_578_))
{
case 0:
{
lean_object* v___x_580_; 
lean_dec_ref(v_isToken_579_);
v___x_580_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_580_;
}
case 1:
{
lean_object* v_pre_581_; 
v_pre_581_ = lean_ctor_get(v_n_578_, 0);
if (lean_obj_tag(v_pre_581_) == 0)
{
lean_object* v_str_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; 
v_str_582_ = lean_ctor_get(v_n_578_, 1);
lean_inc_ref_n(v_str_582_, 2);
lean_dec_ref_known(v_n_578_, 2);
v___x_583_ = lean_apply_1(v_isToken_579_, v_str_582_);
v___x_584_ = lean_unbox(v___x_583_);
v___x_585_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_577_, v_str_582_, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v_str_586_; lean_object* v_r_587_; lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v_r_x27_591_; 
lean_inc(v_pre_581_);
v_str_586_ = lean_ctor_get(v_n_578_, 1);
lean_inc_ref_n(v_str_586_, 2);
lean_dec_ref_known(v_n_578_, 2);
lean_inc_ref(v_isToken_579_);
v_r_587_ = l_Lean_Name_toStringWithSep(v_sep_576_, v_escape_577_, v_pre_581_, v_isToken_579_);
v___x_588_ = lean_string_append(v_r_587_, v_sep_576_);
v___x_589_ = 0;
v___x_590_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_577_, v_str_586_, v___x_589_);
lean_inc_ref(v___x_588_);
v_r_x27_591_ = lean_string_append(v___x_588_, v___x_590_);
lean_dec_ref(v___x_590_);
if (v_escape_577_ == 0)
{
lean_dec_ref(v___x_588_);
lean_dec_ref(v_str_586_);
lean_dec_ref(v_isToken_579_);
return v_r_x27_591_;
}
else
{
lean_object* v___x_592_; uint8_t v___x_593_; 
lean_inc_ref(v_r_x27_591_);
v___x_592_ = lean_apply_1(v_isToken_579_, v_r_x27_591_);
v___x_593_ = lean_unbox(v___x_592_);
if (v___x_593_ == 0)
{
lean_dec_ref(v___x_588_);
lean_dec_ref(v_str_586_);
return v_r_x27_591_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref(v_r_x27_591_);
v___x_594_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_577_, v_str_586_, v_escape_577_);
v___x_595_ = lean_string_append(v___x_588_, v___x_594_);
lean_dec_ref(v___x_594_);
return v___x_595_;
}
}
}
}
default: 
{
lean_object* v_pre_596_; 
lean_dec_ref(v_isToken_579_);
v_pre_596_ = lean_ctor_get(v_n_578_, 0);
if (lean_obj_tag(v_pre_596_) == 0)
{
lean_object* v_i_597_; lean_object* v___x_598_; 
v_i_597_ = lean_ctor_get(v_n_578_, 1);
lean_inc(v_i_597_);
lean_dec_ref_known(v_n_578_, 2);
v___x_598_ = l_Nat_reprFast(v_i_597_);
return v___x_598_;
}
else
{
lean_object* v_i_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_inc(v_pre_596_);
v_i_599_ = lean_ctor_get(v_n_578_, 1);
lean_inc(v_i_599_);
lean_dec_ref_known(v_n_578_, 2);
v___f_600_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_601_ = l_Lean_Name_toStringWithSep(v_sep_576_, v_escape_577_, v_pre_596_, v___f_600_);
v___x_602_ = lean_string_append(v___x_601_, v_sep_576_);
v___x_603_ = l_Nat_reprFast(v_i_599_);
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
lean_dec_ref(v___x_603_);
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_605_, lean_object* v_escape_606_, lean_object* v_n_607_, lean_object* v_isToken_608_){
_start:
{
uint8_t v_escape_boxed_609_; lean_object* v_res_610_; 
v_escape_boxed_609_ = lean_unbox(v_escape_606_);
v_res_610_ = l_Lean_Name_toStringWithSep(v_sep_605_, v_escape_boxed_609_, v_n_607_, v_isToken_608_);
lean_dec_ref(v_sep_605_);
return v_res_610_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; uint8_t v___x_619_; 
v___x_617_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_618_ = lean_name_eq(v_n_616_, v___x_617_);
v___x_619_ = 1;
if (v___x_618_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Name_getRoot(v_n_616_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_str_621_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_str_621_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_str_621_);
lean_dec_ref_known(v___x_620_, 2);
v___x_629_ = lean_string_utf8_byte_size(v_str_621_);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_dec_le(v___x_630_, v___x_629_);
if (v___x_631_ == 0)
{
goto v___jp_622_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_string_memcmp(v_str_621_, v___x_632_, v___x_633_, v___x_633_, v___x_630_);
if (v___x_634_ == 0)
{
goto v___jp_622_;
}
else
{
lean_dec_ref(v_str_621_);
return v___x_619_;
}
}
v___jp_622_:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_string_utf8_byte_size(v_str_621_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_dec_le(v___x_624_, v___x_623_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_str_621_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_string_memcmp(v_str_621_, v___x_626_, v___x_627_, v___x_627_, v___x_624_);
lean_dec_ref(v_str_621_);
return v___x_628_;
}
}
}
else
{
lean_dec(v___x_620_);
return v___x_618_;
}
}
else
{
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_635_);
lean_dec(v_n_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_639_, uint8_t v_escape_640_, lean_object* v_isToken_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_640_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Name_toStringWithSep(v___x_642_, v_escape_640_, v_n_639_, v_isToken_641_);
return v___x_643_;
}
else
{
uint8_t v___x_644_; 
lean_inc(v_n_639_);
v___x_644_ = l_Lean_Name_isInaccessibleUserName(v_n_639_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
v___x_645_ = l_Lean_Name_hasMacroScopes(v_n_639_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
v___x_646_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_639_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Name_toStringWithSep(v___x_642_, v_escape_640_, v_n_639_, v_isToken_641_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Name_toStringWithSep(v___x_642_, v___x_645_, v_n_639_, v_isToken_641_);
return v___x_648_;
}
}
else
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Name_toStringWithSep(v___x_642_, v___x_644_, v_n_639_, v_isToken_641_);
return v___x_649_;
}
}
else
{
uint8_t v___x_650_; lean_object* v___x_651_; 
v___x_650_ = 0;
v___x_651_ = l_Lean_Name_toStringWithSep(v___x_642_, v___x_650_, v_n_639_, v_isToken_641_);
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_652_, lean_object* v_escape_653_, lean_object* v_isToken_654_){
_start:
{
uint8_t v_escape_boxed_655_; lean_object* v_res_656_; 
v_escape_boxed_655_ = lean_unbox(v_escape_653_);
v_res_656_ = l_Lean_Name_toStringWithToken(v_n_652_, v_escape_boxed_655_, v_isToken_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_657_, uint8_t v_escape_658_, lean_object* v_n_659_){
_start:
{
switch(lean_obj_tag(v_n_659_))
{
case 0:
{
lean_object* v___x_660_; 
v___x_660_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_660_;
}
case 1:
{
lean_object* v_pre_661_; 
v_pre_661_ = lean_ctor_get(v_n_659_, 0);
if (lean_obj_tag(v_pre_661_) == 0)
{
lean_object* v_str_662_; uint8_t v___x_663_; lean_object* v___x_664_; 
v_str_662_ = lean_ctor_get(v_n_659_, 1);
lean_inc_ref(v_str_662_);
lean_dec_ref_known(v_n_659_, 2);
v___x_663_ = 0;
v___x_664_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_658_, v_str_662_, v___x_663_);
return v___x_664_;
}
else
{
lean_object* v_str_665_; lean_object* v_r_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v_r_x27_670_; 
lean_inc(v_pre_661_);
v_str_665_ = lean_ctor_get(v_n_659_, 1);
lean_inc_ref(v_str_665_);
lean_dec_ref_known(v_n_659_, 2);
v_r_666_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_657_, v_escape_658_, v_pre_661_);
v___x_667_ = lean_string_append(v_r_666_, v_sep_657_);
v___x_668_ = 0;
v___x_669_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_658_, v_str_665_, v___x_668_);
v_r_x27_670_ = lean_string_append(v___x_667_, v___x_669_);
lean_dec_ref(v___x_669_);
return v_r_x27_670_;
}
}
default: 
{
lean_object* v_pre_671_; 
v_pre_671_ = lean_ctor_get(v_n_659_, 0);
if (lean_obj_tag(v_pre_671_) == 0)
{
lean_object* v_i_672_; lean_object* v___x_673_; 
v_i_672_ = lean_ctor_get(v_n_659_, 1);
lean_inc(v_i_672_);
lean_dec_ref_known(v_n_659_, 2);
v___x_673_ = l_Nat_reprFast(v_i_672_);
return v___x_673_;
}
else
{
lean_object* v_i_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc(v_pre_671_);
v_i_674_ = lean_ctor_get(v_n_659_, 1);
lean_inc(v_i_674_);
lean_dec_ref_known(v_n_659_, 2);
v___x_675_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_657_, v_escape_658_, v_pre_671_);
v___x_676_ = lean_string_append(v___x_675_, v_sep_657_);
v___x_677_ = l_Nat_reprFast(v_i_674_);
v___x_678_ = lean_string_append(v___x_676_, v___x_677_);
lean_dec_ref(v___x_677_);
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_679_, lean_object* v_escape_680_, lean_object* v_n_681_){
_start:
{
uint8_t v_escape_boxed_682_; lean_object* v_res_683_; 
v_escape_boxed_682_ = lean_unbox(v_escape_680_);
v_res_683_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_679_, v_escape_boxed_682_, v_n_681_);
lean_dec_ref(v_sep_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_684_, uint8_t v_escape_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_685_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_686_, v_escape_685_, v_n_684_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
lean_inc(v_n_684_);
v___x_688_ = l_Lean_Name_isInaccessibleUserName(v_n_684_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; 
v___x_689_ = l_Lean_Name_hasMacroScopes(v_n_684_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; 
v___x_690_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_684_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_686_, v_escape_685_, v_n_684_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_686_, v___x_689_, v_n_684_);
return v___x_692_;
}
}
else
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_686_, v___x_688_, v_n_684_);
return v___x_693_;
}
}
else
{
uint8_t v___x_694_; lean_object* v___x_695_; 
v___x_694_ = 0;
v___x_695_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_686_, v___x_694_, v_n_684_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_696_, lean_object* v_escape_697_){
_start:
{
uint8_t v_escape_boxed_698_; lean_object* v_res_699_; 
v_escape_boxed_698_ = lean_unbox(v_escape_697_);
v_res_699_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_696_, v_escape_boxed_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_700_, uint8_t v_escape_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_700_, v_escape_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_703_, lean_object* v_escape_704_){
_start:
{
uint8_t v_escape_boxed_705_; lean_object* v_res_706_; 
v_escape_boxed_705_ = lean_unbox(v_escape_704_);
v_res_706_ = l_Lean_Name_toString(v_n_703_, v_escape_boxed_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_707_){
_start:
{
uint8_t v___x_708_; lean_object* v___x_709_; 
v___x_708_ = 1;
v___x_709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_707_, v___x_708_);
return v___x_709_;
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
