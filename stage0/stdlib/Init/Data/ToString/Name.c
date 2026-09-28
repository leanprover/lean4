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
lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v_startInclusive_97_; lean_object* v_endExclusive_98_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_112_; lean_object* v___y_113_; uint8_t v___y_114_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v___y_117_; uint8_t v___y_118_; uint32_t v___y_132_; uint32_t v___y_137_; uint8_t v___y_138_; uint32_t v___y_144_; lean_object* v___x_160_; uint8_t v_c_161_; uint8_t v___x_170_; uint8_t v___x_171_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v_c_161_ = lean_string_get_byte_fast(v_s_92_, v___x_160_);
v___x_170_ = 97;
v___x_171_ = lean_uint8_dec_le(v___x_170_, v_c_161_);
if (v___x_171_ == 0)
{
goto v___jp_165_;
}
else
{
uint8_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 122;
v___x_173_ = lean_uint8_dec_le(v_c_161_, v___x_172_);
if (v___x_173_ == 0)
{
goto v___jp_165_;
}
else
{
goto v___jp_157_;
}
}
v___jp_93_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v_decide_102_; 
lean_inc_ref(v___y_94_);
v___x_99_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_94_);
v___x_100_ = l_String_Slice_Pos_skipWhile___redArg(v___y_96_, v___y_95_, v___x_99_);
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
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_startInclusive_109_; lean_object* v_endExclusive_110_; 
v___x_107_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_108_ = l_panic___redArg(v___y_106_, v___x_107_);
v_startInclusive_109_ = lean_ctor_get(v___x_108_, 1);
lean_inc(v_startInclusive_109_);
v_endExclusive_110_ = lean_ctor_get(v___x_108_, 2);
lean_inc(v_endExclusive_110_);
v___y_94_ = v___y_104_;
v___y_95_ = v___y_105_;
v___y_96_ = v___x_108_;
v_startInclusive_97_ = v_startInclusive_109_;
v_endExclusive_98_ = v_endExclusive_110_;
goto v___jp_93_;
}
v___jp_111_:
{
if (v___y_114_ == 0)
{
lean_dec(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v_s_92_);
v___y_104_ = v___y_112_;
v___y_105_ = v___y_113_;
v___y_106_ = v___y_115_;
goto v___jp_103_;
}
else
{
if (v___y_118_ == 0)
{
lean_dec(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v_s_92_);
v___y_104_ = v___y_112_;
v___y_105_ = v___y_113_;
v___y_106_ = v___y_115_;
goto v___jp_103_;
}
else
{
lean_object* v___x_119_; 
lean_inc(v___y_117_);
lean_inc(v___y_116_);
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v_s_92_);
lean_ctor_set(v___x_119_, 1, v___y_116_);
lean_ctor_set(v___x_119_, 2, v___y_117_);
v___y_94_ = v___y_112_;
v___y_95_ = v___y_113_;
v___y_96_ = v___x_119_;
v_startInclusive_97_ = v___y_116_;
v_endExclusive_98_ = v___y_117_;
goto v___jp_93_;
}
}
}
v___jp_120_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_string_utf8_byte_size(v_s_92_);
lean_inc_ref(v_s_92_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_s_92_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = l_Substring_Raw_nextn(v___x_123_, v___x_124_, v___x_121_);
lean_dec_ref_known(v___x_123_, 3);
v___x_126_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_127_ = l_String_instInhabitedSlice;
v___x_128_ = lean_string_is_valid_pos(v_s_92_, v___x_125_);
v___x_129_ = lean_string_is_valid_pos(v_s_92_, v___x_122_);
if (v___x_129_ == 0)
{
v___y_112_ = v___x_126_;
v___y_113_ = v___x_121_;
v___y_114_ = v___x_128_;
v___y_115_ = v___x_127_;
v___y_116_ = v___x_125_;
v___y_117_ = v___x_122_;
v___y_118_ = v___x_129_;
goto v___jp_111_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_le(v___x_125_, v___x_122_);
v___y_112_ = v___x_126_;
v___y_113_ = v___x_121_;
v___y_114_ = v___x_128_;
v___y_115_ = v___x_127_;
v___y_116_ = v___x_125_;
v___y_117_ = v___x_122_;
v___y_118_ = v___x_130_;
goto v___jp_111_;
}
}
v___jp_131_:
{
uint32_t v___x_133_; uint8_t v___x_134_; 
v___x_133_ = 95;
v___x_134_ = lean_uint32_dec_eq(v___y_132_, v___x_133_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_isLetterLike(v___y_132_);
if (v___x_135_ == 0)
{
lean_dec_ref(v_s_92_);
return v___x_135_;
}
else
{
goto v___jp_120_;
}
}
else
{
goto v___jp_120_;
}
}
v___jp_136_:
{
if (v___y_138_ == 0)
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 97;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v___y_137_);
if (v___x_140_ == 0)
{
v___y_132_ = v___y_137_;
goto v___jp_131_;
}
else
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 122;
v___x_142_ = lean_uint32_dec_le(v___y_137_, v___x_141_);
if (v___x_142_ == 0)
{
v___y_132_ = v___y_137_;
goto v___jp_131_;
}
else
{
goto v___jp_120_;
}
}
}
else
{
goto v___jp_120_;
}
}
v___jp_143_:
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 65;
v___x_146_ = lean_uint32_dec_le(v___x_145_, v___y_144_);
if (v___x_146_ == 0)
{
v___y_137_ = v___y_144_;
v___y_138_ = v___x_146_;
goto v___jp_136_;
}
else
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 90;
v___x_148_ = lean_uint32_dec_le(v___y_144_, v___x_147_);
v___y_137_ = v___y_144_;
v___y_138_ = v___x_148_;
goto v___jp_136_;
}
}
v___jp_149_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_string_utf8_byte_size(v_s_92_);
lean_inc_ref(v_s_92_);
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v_s_92_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
lean_ctor_set(v___x_152_, 2, v___x_151_);
v___x_153_ = l_String_Slice_Pos_get_x3f(v___x_152_, v___x_150_);
lean_dec_ref_known(v___x_152_, 3);
if (lean_obj_tag(v___x_153_) == 0)
{
uint32_t v___x_154_; 
v___x_154_ = 65;
v___y_144_ = v___x_154_;
goto v___jp_143_;
}
else
{
lean_object* v_val_155_; uint32_t v___x_156_; 
v_val_155_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v___x_153_, 1);
v___x_156_ = lean_unbox_uint32(v_val_155_);
lean_dec(v_val_155_);
v___y_144_ = v___x_156_;
goto v___jp_143_;
}
}
v___jp_157_:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_92_, v___x_158_);
if (v___x_159_ == 0)
{
goto v___jp_149_;
}
else
{
lean_dec_ref(v_s_92_);
return v___x_159_;
}
}
v___jp_162_:
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 95;
v___x_164_ = lean_uint8_dec_eq(v_c_161_, v___x_163_);
if (v___x_164_ == 0)
{
goto v___jp_149_;
}
else
{
goto v___jp_157_;
}
}
v___jp_165_:
{
uint8_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 65;
v___x_167_ = lean_uint8_dec_le(v___x_166_, v_c_161_);
if (v___x_167_ == 0)
{
goto v___jp_162_;
}
else
{
uint8_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 90;
v___x_169_ = lean_uint8_dec_le(v_c_161_, v___x_168_);
if (v___x_169_ == 0)
{
goto v___jp_162_;
}
else
{
goto v___jp_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_177_, lean_object* v_h_178_){
_start:
{
lean_object* v___y_180_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v_startInclusive_183_; lean_object* v_endExclusive_184_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_198_; lean_object* v___y_199_; uint8_t v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; uint8_t v___y_204_; uint32_t v___y_218_; uint32_t v___y_223_; uint8_t v___y_224_; uint32_t v___y_230_; lean_object* v___x_246_; uint8_t v_c_247_; uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v_c_247_ = lean_string_get_byte_fast(v_s_177_, v___x_246_);
v___x_256_ = 97;
v___x_257_ = lean_uint8_dec_le(v___x_256_, v_c_247_);
if (v___x_257_ == 0)
{
goto v___jp_251_;
}
else
{
uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 122;
v___x_259_ = lean_uint8_dec_le(v_c_247_, v___x_258_);
if (v___x_259_ == 0)
{
goto v___jp_251_;
}
else
{
goto v___jp_243_;
}
}
v___jp_179_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v_decide_188_; 
lean_inc_ref(v___y_180_);
v___x_185_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_180_);
v___x_186_ = l_String_Slice_Pos_skipWhile___redArg(v___y_182_, v___y_181_, v___x_185_);
lean_dec_ref(v___y_182_);
v___x_187_ = lean_nat_sub(v_endExclusive_184_, v_startInclusive_183_);
lean_dec(v_startInclusive_183_);
lean_dec(v_endExclusive_184_);
v_decide_188_ = lean_nat_dec_eq(v___x_186_, v___x_187_);
lean_dec(v___x_187_);
lean_dec(v___x_186_);
return v_decide_188_;
}
v___jp_189_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_startInclusive_195_; lean_object* v_endExclusive_196_; 
v___x_193_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_194_ = l_panic___redArg(v___y_192_, v___x_193_);
v_startInclusive_195_ = lean_ctor_get(v___x_194_, 1);
lean_inc(v_startInclusive_195_);
v_endExclusive_196_ = lean_ctor_get(v___x_194_, 2);
lean_inc(v_endExclusive_196_);
v___y_180_ = v___y_190_;
v___y_181_ = v___y_191_;
v___y_182_ = v___x_194_;
v_startInclusive_183_ = v_startInclusive_195_;
v_endExclusive_184_ = v_endExclusive_196_;
goto v___jp_179_;
}
v___jp_197_:
{
if (v___y_200_ == 0)
{
lean_dec(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v_s_177_);
v___y_190_ = v___y_198_;
v___y_191_ = v___y_199_;
v___y_192_ = v___y_201_;
goto v___jp_189_;
}
else
{
if (v___y_204_ == 0)
{
lean_dec(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v_s_177_);
v___y_190_ = v___y_198_;
v___y_191_ = v___y_199_;
v___y_192_ = v___y_201_;
goto v___jp_189_;
}
else
{
lean_object* v___x_205_; 
lean_inc(v___y_203_);
lean_inc(v___y_202_);
v___x_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_205_, 0, v_s_177_);
lean_ctor_set(v___x_205_, 1, v___y_202_);
lean_ctor_set(v___x_205_, 2, v___y_203_);
v___y_180_ = v___y_198_;
v___y_181_ = v___y_199_;
v___y_182_ = v___x_205_;
v_startInclusive_183_ = v___y_202_;
v_endExclusive_184_ = v___y_203_;
goto v___jp_179_;
}
}
}
v___jp_206_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_string_utf8_byte_size(v_s_177_);
lean_inc_ref(v_s_177_);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v_s_177_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
lean_ctor_set(v___x_209_, 2, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = l_Substring_Raw_nextn(v___x_209_, v___x_210_, v___x_207_);
lean_dec_ref_known(v___x_209_, 3);
v___x_212_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_213_ = l_String_instInhabitedSlice;
v___x_214_ = lean_string_is_valid_pos(v_s_177_, v___x_211_);
v___x_215_ = lean_string_is_valid_pos(v_s_177_, v___x_208_);
if (v___x_215_ == 0)
{
v___y_198_ = v___x_212_;
v___y_199_ = v___x_207_;
v___y_200_ = v___x_214_;
v___y_201_ = v___x_213_;
v___y_202_ = v___x_211_;
v___y_203_ = v___x_208_;
v___y_204_ = v___x_215_;
goto v___jp_197_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_le(v___x_211_, v___x_208_);
v___y_198_ = v___x_212_;
v___y_199_ = v___x_207_;
v___y_200_ = v___x_214_;
v___y_201_ = v___x_213_;
v___y_202_ = v___x_211_;
v___y_203_ = v___x_208_;
v___y_204_ = v___x_216_;
goto v___jp_197_;
}
}
v___jp_217_:
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 95;
v___x_220_ = lean_uint32_dec_eq(v___y_218_, v___x_219_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
v___x_221_ = l_Lean_isLetterLike(v___y_218_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_s_177_);
return v___x_221_;
}
else
{
goto v___jp_206_;
}
}
else
{
goto v___jp_206_;
}
}
v___jp_222_:
{
if (v___y_224_ == 0)
{
uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 97;
v___x_226_ = lean_uint32_dec_le(v___x_225_, v___y_223_);
if (v___x_226_ == 0)
{
v___y_218_ = v___y_223_;
goto v___jp_217_;
}
else
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 122;
v___x_228_ = lean_uint32_dec_le(v___y_223_, v___x_227_);
if (v___x_228_ == 0)
{
v___y_218_ = v___y_223_;
goto v___jp_217_;
}
else
{
goto v___jp_206_;
}
}
}
else
{
goto v___jp_206_;
}
}
v___jp_229_:
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 65;
v___x_232_ = lean_uint32_dec_le(v___x_231_, v___y_230_);
if (v___x_232_ == 0)
{
v___y_223_ = v___y_230_;
v___y_224_ = v___x_232_;
goto v___jp_222_;
}
else
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 90;
v___x_234_ = lean_uint32_dec_le(v___y_230_, v___x_233_);
v___y_223_ = v___y_230_;
v___y_224_ = v___x_234_;
goto v___jp_222_;
}
}
v___jp_235_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_string_utf8_byte_size(v_s_177_);
lean_inc_ref(v_s_177_);
v___x_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_238_, 0, v_s_177_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
v___x_239_ = l_String_Slice_Pos_get_x3f(v___x_238_, v___x_236_);
lean_dec_ref_known(v___x_238_, 3);
if (lean_obj_tag(v___x_239_) == 0)
{
uint32_t v___x_240_; 
v___x_240_ = 65;
v___y_230_ = v___x_240_;
goto v___jp_229_;
}
else
{
lean_object* v_val_241_; uint32_t v___x_242_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_239_, 1);
v___x_242_ = lean_unbox_uint32(v_val_241_);
lean_dec(v_val_241_);
v___y_230_ = v___x_242_;
goto v___jp_229_;
}
}
v___jp_243_:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_177_, v___x_244_);
if (v___x_245_ == 0)
{
goto v___jp_235_;
}
else
{
lean_dec_ref(v_s_177_);
return v___x_245_;
}
}
v___jp_248_:
{
uint8_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 95;
v___x_250_ = lean_uint8_dec_eq(v_c_247_, v___x_249_);
if (v___x_250_ == 0)
{
goto v___jp_235_;
}
else
{
goto v___jp_243_;
}
}
v___jp_251_:
{
uint8_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 65;
v___x_253_ = lean_uint8_dec_le(v___x_252_, v_c_247_);
if (v___x_253_ == 0)
{
goto v___jp_248_;
}
else
{
uint8_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 90;
v___x_255_ = lean_uint8_dec_le(v_c_247_, v___x_254_);
if (v___x_255_ == 0)
{
goto v___jp_248_;
}
else
{
goto v___jp_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_260_, lean_object* v_h_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_260_, v_h_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = l_Lean_idBeginEscape;
v___x_266_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_267_ = lean_string_push(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = l_Lean_idEndEscape;
v___x_269_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_270_ = lean_string_push(v___x_269_, v___x_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_273_ = lean_string_append(v___x_272_, v_s_271_);
v___x_274_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_276_);
lean_dec_ref(v_s_276_);
return v_res_277_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_280_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_289_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_281_, v___x_288_, v___y_282_, lean_box(0), lean_box(0), v___y_285_, v___y_286_, v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_293_, uint8_t v_force_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_string_utf8_byte_size(v_s_293_);
v___x_297_ = lean_nat_dec_lt(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_299_ = lean_string_append(v___x_298_, v_s_293_);
lean_dec_ref(v_s_293_);
v___x_300_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v___f_303_; uint8_t v___y_315_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v_startInclusive_321_; lean_object* v_endExclusive_322_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_336_; lean_object* v___y_337_; uint8_t v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; uint32_t v___y_354_; uint32_t v___y_359_; uint8_t v___y_360_; uint32_t v___y_366_; 
v___f_303_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_294_ == 0)
{
uint8_t v_c_380_; uint8_t v___x_389_; uint8_t v___x_390_; 
v_c_380_ = lean_string_get_byte_fast(v_s_293_, v___x_295_);
v___x_389_ = 97;
v___x_390_ = lean_uint8_dec_le(v___x_389_, v_c_380_);
if (v___x_390_ == 0)
{
goto v___jp_384_;
}
else
{
uint8_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 122;
v___x_392_ = lean_uint8_dec_le(v_c_380_, v___x_391_);
if (v___x_392_ == 0)
{
goto v___jp_384_;
}
else
{
goto v___jp_377_;
}
}
v___jp_381_:
{
uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 95;
v___x_383_ = lean_uint8_dec_eq(v_c_380_, v___x_382_);
if (v___x_383_ == 0)
{
goto v___jp_371_;
}
else
{
goto v___jp_377_;
}
}
v___jp_384_:
{
uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 65;
v___x_386_ = lean_uint8_dec_le(v___x_385_, v_c_380_);
if (v___x_386_ == 0)
{
goto v___jp_381_;
}
else
{
uint8_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 90;
v___x_388_ = lean_uint8_dec_le(v_c_380_, v___x_387_);
if (v___x_388_ == 0)
{
goto v___jp_381_;
}
else
{
goto v___jp_377_;
}
}
}
}
else
{
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_293_);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v_s_293_);
lean_ctor_set(v___x_306_, 1, v___x_295_);
lean_ctor_set(v___x_306_, 2, v___x_296_);
v___x_307_ = l_String_Slice_contains___redArg(v___f_303_, v___x_306_, v___x_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_308_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_309_ = lean_string_append(v___x_308_, v_s_293_);
lean_dec_ref(v_s_293_);
v___x_310_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
lean_dec_ref(v_s_293_);
v___x_313_ = lean_box(0);
return v___x_313_;
}
}
v___jp_314_:
{
if (v___y_315_ == 0)
{
goto v___jp_304_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_s_293_);
return v___x_316_;
}
}
v___jp_317_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v_decide_326_; 
lean_inc_ref(v___y_318_);
v___x_323_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_318_);
v___x_324_ = l_String_Slice_Pos_skipWhile___redArg(v___y_320_, v___y_319_, v___x_323_);
lean_dec_ref(v___y_320_);
v___x_325_ = lean_nat_sub(v_endExclusive_322_, v_startInclusive_321_);
lean_dec(v_startInclusive_321_);
lean_dec(v_endExclusive_322_);
v_decide_326_ = lean_nat_dec_eq(v___x_324_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v___x_324_);
v___y_315_ = v_decide_326_;
goto v___jp_314_;
}
v___jp_327_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_startInclusive_333_; lean_object* v_endExclusive_334_; 
v___x_331_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_332_ = l_panic___redArg(v___y_330_, v___x_331_);
v_startInclusive_333_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_startInclusive_333_);
v_endExclusive_334_ = lean_ctor_get(v___x_332_, 2);
lean_inc(v_endExclusive_334_);
v___y_318_ = v___y_328_;
v___y_319_ = v___y_329_;
v___y_320_ = v___x_332_;
v_startInclusive_321_ = v_startInclusive_333_;
v_endExclusive_322_ = v_endExclusive_334_;
goto v___jp_317_;
}
v___jp_335_:
{
if (v___y_338_ == 0)
{
lean_dec(v___y_340_);
lean_dec(v___y_339_);
v___y_328_ = v___y_336_;
v___y_329_ = v___y_337_;
v___y_330_ = v___y_341_;
goto v___jp_327_;
}
else
{
if (v___y_342_ == 0)
{
lean_dec(v___y_340_);
lean_dec(v___y_339_);
v___y_328_ = v___y_336_;
v___y_329_ = v___y_337_;
v___y_330_ = v___y_341_;
goto v___jp_327_;
}
else
{
lean_object* v___x_343_; 
lean_inc(v___y_340_);
lean_inc(v___y_339_);
lean_inc_ref(v_s_293_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_s_293_);
lean_ctor_set(v___x_343_, 1, v___y_339_);
lean_ctor_set(v___x_343_, 2, v___y_340_);
v___y_318_ = v___y_336_;
v___y_319_ = v___y_337_;
v___y_320_ = v___x_343_;
v_startInclusive_321_ = v___y_339_;
v_endExclusive_322_ = v___y_340_;
goto v___jp_317_;
}
}
}
v___jp_344_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; uint8_t v___x_351_; 
lean_inc_ref(v_s_293_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v_s_293_);
lean_ctor_set(v___x_345_, 1, v___x_295_);
lean_ctor_set(v___x_345_, 2, v___x_296_);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = l_Substring_Raw_nextn(v___x_345_, v___x_346_, v___x_295_);
lean_dec_ref_known(v___x_345_, 3);
v___x_348_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_349_ = l_String_instInhabitedSlice;
v___x_350_ = lean_string_is_valid_pos(v_s_293_, v___x_347_);
v___x_351_ = lean_string_is_valid_pos(v_s_293_, v___x_296_);
if (v___x_351_ == 0)
{
v___y_336_ = v___x_348_;
v___y_337_ = v___x_295_;
v___y_338_ = v___x_350_;
v___y_339_ = v___x_347_;
v___y_340_ = v___x_296_;
v___y_341_ = v___x_349_;
v___y_342_ = v___x_351_;
goto v___jp_335_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_le(v___x_347_, v___x_296_);
v___y_336_ = v___x_348_;
v___y_337_ = v___x_295_;
v___y_338_ = v___x_350_;
v___y_339_ = v___x_347_;
v___y_340_ = v___x_296_;
v___y_341_ = v___x_349_;
v___y_342_ = v___x_352_;
goto v___jp_335_;
}
}
v___jp_353_:
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 95;
v___x_356_ = lean_uint32_dec_eq(v___y_354_, v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_isLetterLike(v___y_354_);
if (v___x_357_ == 0)
{
v___y_315_ = v___x_357_;
goto v___jp_314_;
}
else
{
goto v___jp_344_;
}
}
else
{
goto v___jp_344_;
}
}
v___jp_358_:
{
if (v___y_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 97;
v___x_362_ = lean_uint32_dec_le(v___x_361_, v___y_359_);
if (v___x_362_ == 0)
{
v___y_354_ = v___y_359_;
goto v___jp_353_;
}
else
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 122;
v___x_364_ = lean_uint32_dec_le(v___y_359_, v___x_363_);
if (v___x_364_ == 0)
{
v___y_354_ = v___y_359_;
goto v___jp_353_;
}
else
{
goto v___jp_344_;
}
}
}
else
{
goto v___jp_344_;
}
}
v___jp_365_:
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 65;
v___x_368_ = lean_uint32_dec_le(v___x_367_, v___y_366_);
if (v___x_368_ == 0)
{
v___y_359_ = v___y_366_;
v___y_360_ = v___x_368_;
goto v___jp_358_;
}
else
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 90;
v___x_370_ = lean_uint32_dec_le(v___y_366_, v___x_369_);
v___y_359_ = v___y_366_;
v___y_360_ = v___x_370_;
goto v___jp_358_;
}
}
v___jp_371_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_inc_ref(v_s_293_);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v_s_293_);
lean_ctor_set(v___x_372_, 1, v___x_295_);
lean_ctor_set(v___x_372_, 2, v___x_296_);
v___x_373_ = l_String_Slice_Pos_get_x3f(v___x_372_, v___x_295_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_373_) == 0)
{
uint32_t v___x_374_; 
v___x_374_ = 65;
v___y_366_ = v___x_374_;
goto v___jp_365_;
}
else
{
lean_object* v_val_375_; uint32_t v___x_376_; 
v_val_375_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v___x_373_, 1);
v___x_376_ = lean_unbox_uint32(v_val_375_);
lean_dec(v_val_375_);
v___y_366_ = v___x_376_;
goto v___jp_365_;
}
}
v___jp_377_:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_293_, v___x_378_);
if (v___x_379_ == 0)
{
goto v___jp_371_;
}
else
{
v___y_315_ = v___x_379_;
goto v___jp_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_393_, lean_object* v_force_394_){
_start:
{
uint8_t v_force_boxed_395_; lean_object* v_res_396_; 
v_force_boxed_395_ = lean_unbox(v_force_394_);
v_res_396_ = l_Lean_Name_escapePart(v_s_393_, v_force_boxed_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = l_String_instInhabitedSlice;
v___x_399_ = lean_panic_fn_borrowed(v___x_398_, v_msg_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_400_, lean_object* v_pos_401_){
_start:
{
lean_object* v_str_402_; lean_object* v_startInclusive_403_; lean_object* v_endExclusive_404_; lean_object* v___x_405_; uint8_t v___y_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v_decide_418_; 
v_str_402_ = lean_ctor_get(v_s_400_, 0);
v_startInclusive_403_ = lean_ctor_get(v_s_400_, 1);
v_endExclusive_404_ = lean_ctor_get(v_s_400_, 2);
v___x_405_ = lean_nat_add(v_startInclusive_403_, v_pos_401_);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_nat_sub(v_endExclusive_404_, v___x_405_);
v_decide_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
lean_dec(v___x_417_);
if (v_decide_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___y_437_; uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_419_ = lean_string_utf8_get_fast(v_str_402_, v___x_405_);
v___x_442_ = 65;
v___x_443_ = lean_uint32_dec_le(v___x_442_, v___x_419_);
if (v___x_443_ == 0)
{
v___y_437_ = v___x_443_;
goto v___jp_436_;
}
else
{
uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = 90;
v___x_445_ = lean_uint32_dec_le(v___x_419_, v___x_444_);
v___y_437_ = v___x_445_;
goto v___jp_436_;
}
v___jp_420_:
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 95;
v___x_422_ = lean_uint32_dec_eq(v___x_419_, v___x_421_);
if (v___x_422_ == 0)
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 39;
v___x_424_ = lean_uint32_dec_eq(v___x_419_, v___x_423_);
if (v___x_424_ == 0)
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 33;
v___x_426_ = lean_uint32_dec_eq(v___x_419_, v___x_425_);
if (v___x_426_ == 0)
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 63;
v___x_428_ = lean_uint32_dec_eq(v___x_419_, v___x_427_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_isLetterLike(v___x_419_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; 
v___x_430_ = l_Lean_isSubScriptAlnum(v___x_419_);
v___y_415_ = v___x_430_;
goto v___jp_414_;
}
else
{
v___y_415_ = v___x_429_;
goto v___jp_414_;
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
else
{
goto v___jp_406_;
}
}
v___jp_431_:
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 48;
v___x_433_ = lean_uint32_dec_le(v___x_432_, v___x_419_);
if (v___x_433_ == 0)
{
goto v___jp_420_;
}
else
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 57;
v___x_435_ = lean_uint32_dec_le(v___x_419_, v___x_434_);
if (v___x_435_ == 0)
{
goto v___jp_420_;
}
else
{
goto v___jp_406_;
}
}
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 97;
v___x_439_ = lean_uint32_dec_le(v___x_438_, v___x_419_);
if (v___x_439_ == 0)
{
goto v___jp_431_;
}
else
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 122;
v___x_441_ = lean_uint32_dec_le(v___x_419_, v___x_440_);
if (v___x_441_ == 0)
{
goto v___jp_431_;
}
else
{
goto v___jp_406_;
}
}
}
else
{
goto v___jp_406_;
}
}
}
else
{
lean_dec(v___x_405_);
return v_pos_401_;
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_407_ = lean_string_utf8_next_fast(v_str_402_, v___x_405_);
v___x_408_ = lean_nat_sub(v___x_407_, v___x_405_);
lean_dec(v___x_405_);
v___x_409_ = lean_nat_add(v_pos_401_, v___x_408_);
lean_dec(v___x_408_);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_pos_401_, v___x_410_);
v___x_412_ = lean_nat_dec_le(v___x_411_, v___x_409_);
lean_dec(v___x_411_);
if (v___x_412_ == 0)
{
lean_dec(v___x_409_);
return v_pos_401_;
}
else
{
lean_dec(v_pos_401_);
v_pos_401_ = v___x_409_;
goto _start;
}
}
v___jp_414_:
{
if (v___y_415_ == 0)
{
lean_dec(v___x_405_);
return v_pos_401_;
}
else
{
goto v___jp_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_446_, lean_object* v_pos_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_446_, v_pos_447_);
lean_dec_ref(v_s_446_);
return v_res_448_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_449_, lean_object* v_a_450_, uint8_t v_b_451_){
_start:
{
lean_object* v_str_452_; lean_object* v_startInclusive_453_; lean_object* v_endExclusive_454_; lean_object* v___x_455_; uint8_t v_decide_456_; 
v_str_452_ = lean_ctor_get(v_s_449_, 0);
v_startInclusive_453_ = lean_ctor_get(v_s_449_, 1);
v_endExclusive_454_ = lean_ctor_get(v_s_449_, 2);
v___x_455_ = lean_nat_sub(v_endExclusive_454_, v_startInclusive_453_);
v_decide_456_ = lean_nat_dec_eq(v_a_450_, v___x_455_);
lean_dec(v___x_455_);
if (v_decide_456_ == 0)
{
lean_object* v___x_457_; uint32_t v___x_458_; uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_457_ = lean_nat_add(v_startInclusive_453_, v_a_450_);
lean_dec(v_a_450_);
v___x_458_ = lean_string_utf8_get_fast(v_str_452_, v___x_457_);
v___x_459_ = l_Lean_idEndEscape;
v___x_460_ = lean_uint32_dec_eq(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_string_utf8_next_fast(v_str_452_, v___x_457_);
lean_dec(v___x_457_);
v___x_462_ = lean_nat_sub(v___x_461_, v_startInclusive_453_);
v_a_450_ = v___x_462_;
v_b_451_ = v___x_460_;
goto _start;
}
else
{
lean_dec(v___x_457_);
return v___x_460_;
}
}
else
{
lean_dec(v_a_450_);
return v_b_451_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_464_, lean_object* v_a_465_, lean_object* v_b_466_){
_start:
{
uint8_t v_b_boxed_467_; uint8_t v_res_468_; lean_object* v_r_469_; 
v_b_boxed_467_ = lean_unbox(v_b_466_);
v_res_468_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_464_, v_a_465_, v_b_boxed_467_);
lean_dec_ref(v_s_464_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_470_){
_start:
{
lean_object* v_searcher_471_; uint8_t v___x_472_; uint8_t v___x_473_; 
v_searcher_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = 0;
v___x_473_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_470_, v_searcher_471_, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_474_);
lean_dec_ref(v_s_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_477_, lean_object* v_s_478_, uint8_t v_force_479_){
_start:
{
uint8_t v___y_490_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v_startInclusive_494_; lean_object* v_endExclusive_495_; lean_object* v___y_500_; lean_object* v___y_506_; lean_object* v___y_507_; uint8_t v___y_508_; lean_object* v___y_509_; uint8_t v___y_510_; uint32_t v___y_522_; uint32_t v___y_527_; uint8_t v___y_528_; uint32_t v___y_534_; 
if (v_escape_477_ == 0)
{
return v_s_478_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_string_utf8_byte_size(v_s_478_);
v___x_552_ = lean_nat_dec_lt(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_554_ = lean_string_append(v___x_553_, v_s_478_);
lean_dec_ref(v_s_478_);
v___x_555_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
return v___x_556_;
}
else
{
if (v_force_479_ == 0)
{
uint8_t v_c_557_; uint8_t v___x_566_; uint8_t v___x_567_; 
v_c_557_ = lean_string_get_byte_fast(v_s_478_, v___x_550_);
v___x_566_ = 97;
v___x_567_ = lean_uint8_dec_le(v___x_566_, v_c_557_);
if (v___x_567_ == 0)
{
goto v___jp_561_;
}
else
{
uint8_t v___x_568_; uint8_t v___x_569_; 
v___x_568_ = 122;
v___x_569_ = lean_uint8_dec_le(v_c_557_, v___x_568_);
if (v___x_569_ == 0)
{
goto v___jp_561_;
}
else
{
goto v___jp_547_;
}
}
v___jp_558_:
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 95;
v___x_560_ = lean_uint8_dec_eq(v_c_557_, v___x_559_);
if (v___x_560_ == 0)
{
goto v___jp_539_;
}
else
{
goto v___jp_547_;
}
}
v___jp_561_:
{
uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 65;
v___x_563_ = lean_uint8_dec_le(v___x_562_, v_c_557_);
if (v___x_563_ == 0)
{
goto v___jp_558_;
}
else
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = 90;
v___x_565_ = lean_uint8_dec_le(v_c_557_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_558_;
}
else
{
goto v___jp_547_;
}
}
}
}
else
{
goto v___jp_480_;
}
}
}
v___jp_480_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_string_utf8_byte_size(v_s_478_);
lean_inc_ref(v_s_478_);
v___x_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_483_, 0, v_s_478_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
v___x_484_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_483_);
lean_dec_ref_known(v___x_483_, 3);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_486_ = lean_string_append(v___x_485_, v_s_478_);
lean_dec_ref(v_s_478_);
v___x_487_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
return v___x_488_;
}
else
{
return v_s_478_;
}
}
v___jp_489_:
{
if (v___y_490_ == 0)
{
goto v___jp_480_;
}
else
{
return v_s_478_;
}
}
v___jp_491_:
{
lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v_decide_498_; 
v___x_496_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_493_, v___y_492_);
lean_dec_ref(v___y_493_);
v___x_497_ = lean_nat_sub(v_endExclusive_495_, v_startInclusive_494_);
lean_dec(v_startInclusive_494_);
lean_dec(v_endExclusive_495_);
v_decide_498_ = lean_nat_dec_eq(v___x_496_, v___x_497_);
lean_dec(v___x_497_);
lean_dec(v___x_496_);
v___y_490_ = v_decide_498_;
goto v___jp_489_;
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_startInclusive_503_; lean_object* v_endExclusive_504_; 
v___x_501_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_502_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_501_);
v_startInclusive_503_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_startInclusive_503_);
v_endExclusive_504_ = lean_ctor_get(v___x_502_, 2);
lean_inc(v_endExclusive_504_);
v___y_492_ = v___y_500_;
v___y_493_ = v___x_502_;
v_startInclusive_494_ = v_startInclusive_503_;
v_endExclusive_495_ = v_endExclusive_504_;
goto v___jp_491_;
}
v___jp_505_:
{
if (v___y_508_ == 0)
{
lean_dec(v___y_509_);
lean_dec(v___y_506_);
v___y_500_ = v___y_507_;
goto v___jp_499_;
}
else
{
if (v___y_510_ == 0)
{
lean_dec(v___y_509_);
lean_dec(v___y_506_);
v___y_500_ = v___y_507_;
goto v___jp_499_;
}
else
{
lean_object* v___x_511_; 
lean_inc(v___y_509_);
lean_inc(v___y_506_);
lean_inc_ref(v_s_478_);
v___x_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_511_, 0, v_s_478_);
lean_ctor_set(v___x_511_, 1, v___y_506_);
lean_ctor_set(v___x_511_, 2, v___y_509_);
v___y_492_ = v___y_507_;
v___y_493_ = v___x_511_;
v_startInclusive_494_ = v___y_506_;
v_endExclusive_495_ = v___y_509_;
goto v___jp_491_;
}
}
}
v___jp_512_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; uint8_t v___x_519_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_string_utf8_byte_size(v_s_478_);
lean_inc_ref(v_s_478_);
v___x_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_515_, 0, v_s_478_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_514_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = l_Substring_Raw_nextn(v___x_515_, v___x_516_, v___x_513_);
lean_dec_ref_known(v___x_515_, 3);
v___x_518_ = lean_string_is_valid_pos(v_s_478_, v___x_517_);
v___x_519_ = lean_string_is_valid_pos(v_s_478_, v___x_514_);
if (v___x_519_ == 0)
{
v___y_506_ = v___x_517_;
v___y_507_ = v___x_513_;
v___y_508_ = v___x_518_;
v___y_509_ = v___x_514_;
v___y_510_ = v___x_519_;
goto v___jp_505_;
}
else
{
uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_le(v___x_517_, v___x_514_);
v___y_506_ = v___x_517_;
v___y_507_ = v___x_513_;
v___y_508_ = v___x_518_;
v___y_509_ = v___x_514_;
v___y_510_ = v___x_520_;
goto v___jp_505_;
}
}
v___jp_521_:
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = 95;
v___x_524_ = lean_uint32_dec_eq(v___y_522_, v___x_523_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_isLetterLike(v___y_522_);
if (v___x_525_ == 0)
{
v___y_490_ = v___x_525_;
goto v___jp_489_;
}
else
{
goto v___jp_512_;
}
}
else
{
goto v___jp_512_;
}
}
v___jp_526_:
{
if (v___y_528_ == 0)
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 97;
v___x_530_ = lean_uint32_dec_le(v___x_529_, v___y_527_);
if (v___x_530_ == 0)
{
v___y_522_ = v___y_527_;
goto v___jp_521_;
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 122;
v___x_532_ = lean_uint32_dec_le(v___y_527_, v___x_531_);
if (v___x_532_ == 0)
{
v___y_522_ = v___y_527_;
goto v___jp_521_;
}
else
{
goto v___jp_512_;
}
}
}
else
{
goto v___jp_512_;
}
}
v___jp_533_:
{
uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 65;
v___x_536_ = lean_uint32_dec_le(v___x_535_, v___y_534_);
if (v___x_536_ == 0)
{
v___y_527_ = v___y_534_;
v___y_528_ = v___x_536_;
goto v___jp_526_;
}
else
{
uint32_t v___x_537_; uint8_t v___x_538_; 
v___x_537_ = 90;
v___x_538_ = lean_uint32_dec_le(v___y_534_, v___x_537_);
v___y_527_ = v___y_534_;
v___y_528_ = v___x_538_;
goto v___jp_526_;
}
}
v___jp_539_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_string_utf8_byte_size(v_s_478_);
lean_inc_ref(v_s_478_);
v___x_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_542_, 0, v_s_478_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_541_);
v___x_543_ = l_String_Slice_Pos_get_x3f(v___x_542_, v___x_540_);
lean_dec_ref_known(v___x_542_, 3);
if (lean_obj_tag(v___x_543_) == 0)
{
uint32_t v___x_544_; 
v___x_544_ = 65;
v___y_534_ = v___x_544_;
goto v___jp_533_;
}
else
{
lean_object* v_val_545_; uint32_t v___x_546_; 
v_val_545_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_543_, 1);
v___x_546_ = lean_unbox_uint32(v_val_545_);
lean_dec(v_val_545_);
v___y_534_ = v___x_546_;
goto v___jp_533_;
}
}
v___jp_547_:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_478_, v___x_548_);
if (v___x_549_ == 0)
{
goto v___jp_539_;
}
else
{
v___y_490_ = v___x_549_;
goto v___jp_489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_570_, lean_object* v_s_571_, lean_object* v_force_572_){
_start:
{
uint8_t v_escape_boxed_573_; uint8_t v_force_boxed_574_; lean_object* v_res_575_; 
v_escape_boxed_573_ = lean_unbox(v_escape_570_);
v_force_boxed_574_ = lean_unbox(v_force_572_);
v_res_575_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_573_, v_s_571_, v_force_boxed_574_);
return v_res_575_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_576_, lean_object* v_inst_577_, lean_object* v_R_578_, lean_object* v_a_579_, uint8_t v_b_580_, lean_object* v_c_581_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_576_, v_a_579_, v_b_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_583_, lean_object* v_inst_584_, lean_object* v_R_585_, lean_object* v_a_586_, lean_object* v_b_587_, lean_object* v_c_588_){
_start:
{
uint8_t v_b_boxed_589_; uint8_t v_res_590_; lean_object* v_r_591_; 
v_b_boxed_589_ = lean_unbox(v_b_587_);
v_res_590_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_583_, v_inst_584_, v_R_585_, v_a_586_, v_b_boxed_589_, v_c_588_);
lean_dec_ref(v_s_583_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Lean_Name_toStringWithSep___lam__0(v_x_594_);
lean_dec_ref(v_x_594_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_599_, uint8_t v_escape_600_, lean_object* v_n_601_, lean_object* v_isToken_602_){
_start:
{
switch(lean_obj_tag(v_n_601_))
{
case 0:
{
lean_object* v___x_603_; 
lean_dec_ref(v_isToken_602_);
v___x_603_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_603_;
}
case 1:
{
lean_object* v_pre_604_; 
v_pre_604_ = lean_ctor_get(v_n_601_, 0);
if (lean_obj_tag(v_pre_604_) == 0)
{
lean_object* v_str_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; 
v_str_605_ = lean_ctor_get(v_n_601_, 1);
lean_inc_ref_n(v_str_605_, 2);
lean_dec_ref_known(v_n_601_, 2);
v___x_606_ = lean_apply_1(v_isToken_602_, v_str_605_);
v___x_607_ = lean_unbox(v___x_606_);
v___x_608_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_600_, v_str_605_, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_str_609_; lean_object* v_r_610_; lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v_r_x27_614_; 
lean_inc(v_pre_604_);
v_str_609_ = lean_ctor_get(v_n_601_, 1);
lean_inc_ref_n(v_str_609_, 2);
lean_dec_ref_known(v_n_601_, 2);
lean_inc_ref(v_isToken_602_);
v_r_610_ = l_Lean_Name_toStringWithSep(v_sep_599_, v_escape_600_, v_pre_604_, v_isToken_602_);
v___x_611_ = lean_string_append(v_r_610_, v_sep_599_);
v___x_612_ = 0;
v___x_613_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_600_, v_str_609_, v___x_612_);
lean_inc_ref(v___x_611_);
v_r_x27_614_ = lean_string_append(v___x_611_, v___x_613_);
lean_dec_ref(v___x_613_);
if (v_escape_600_ == 0)
{
lean_dec_ref(v___x_611_);
lean_dec_ref(v_str_609_);
lean_dec_ref(v_isToken_602_);
return v_r_x27_614_;
}
else
{
lean_object* v___x_615_; uint8_t v___x_616_; 
lean_inc_ref(v_r_x27_614_);
v___x_615_ = lean_apply_1(v_isToken_602_, v_r_x27_614_);
v___x_616_ = lean_unbox(v___x_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_611_);
lean_dec_ref(v_str_609_);
return v_r_x27_614_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec_ref(v_r_x27_614_);
v___x_617_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_600_, v_str_609_, v_escape_600_);
v___x_618_ = lean_string_append(v___x_611_, v___x_617_);
lean_dec_ref(v___x_617_);
return v___x_618_;
}
}
}
}
default: 
{
lean_object* v_pre_619_; 
lean_dec_ref(v_isToken_602_);
v_pre_619_ = lean_ctor_get(v_n_601_, 0);
if (lean_obj_tag(v_pre_619_) == 0)
{
lean_object* v_i_620_; lean_object* v___x_621_; 
v_i_620_ = lean_ctor_get(v_n_601_, 1);
lean_inc(v_i_620_);
lean_dec_ref_known(v_n_601_, 2);
v___x_621_ = l_Nat_reprFast(v_i_620_);
return v___x_621_;
}
else
{
lean_object* v_i_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_inc(v_pre_619_);
v_i_622_ = lean_ctor_get(v_n_601_, 1);
lean_inc(v_i_622_);
lean_dec_ref_known(v_n_601_, 2);
v___f_623_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_624_ = l_Lean_Name_toStringWithSep(v_sep_599_, v_escape_600_, v_pre_619_, v___f_623_);
v___x_625_ = lean_string_append(v___x_624_, v_sep_599_);
v___x_626_ = l_Nat_reprFast(v_i_622_);
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
lean_dec_ref(v___x_626_);
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_628_, lean_object* v_escape_629_, lean_object* v_n_630_, lean_object* v_isToken_631_){
_start:
{
uint8_t v_escape_boxed_632_; lean_object* v_res_633_; 
v_escape_boxed_632_ = lean_unbox(v_escape_629_);
v_res_633_ = l_Lean_Name_toStringWithSep(v_sep_628_, v_escape_boxed_632_, v_n_630_, v_isToken_631_);
lean_dec_ref(v_sep_628_);
return v_res_633_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_639_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_640_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_641_ = lean_name_eq(v_n_639_, v___x_640_);
v___x_642_ = 1;
if (v___x_641_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Name_getRoot(v_n_639_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_str_644_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_str_644_ = lean_ctor_get(v___x_643_, 1);
lean_inc_ref(v_str_644_);
lean_dec_ref_known(v___x_643_, 2);
v___x_652_ = lean_string_utf8_byte_size(v_str_644_);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_dec_le(v___x_653_, v___x_652_);
if (v___x_654_ == 0)
{
goto v___jp_645_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_string_memcmp(v_str_644_, v___x_655_, v___x_656_, v___x_656_, v___x_653_);
if (v___x_657_ == 0)
{
goto v___jp_645_;
}
else
{
lean_dec_ref(v_str_644_);
return v___x_642_;
}
}
v___jp_645_:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_string_utf8_byte_size(v_str_644_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_dec_le(v___x_647_, v___x_646_);
if (v___x_648_ == 0)
{
lean_dec_ref(v_str_644_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_string_memcmp(v_str_644_, v___x_649_, v___x_650_, v___x_650_, v___x_647_);
lean_dec_ref(v_str_644_);
return v___x_651_;
}
}
}
else
{
lean_dec(v___x_643_);
return v___x_641_;
}
}
else
{
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_658_);
lean_dec(v_n_658_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_662_, uint8_t v_escape_663_, lean_object* v_isToken_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_663_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Name_toStringWithSep(v___x_665_, v_escape_663_, v_n_662_, v_isToken_664_);
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
lean_inc(v_n_662_);
v___x_667_ = l_Lean_Name_isInaccessibleUserName(v_n_662_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
v___x_668_ = l_Lean_Name_hasMacroScopes(v_n_662_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; 
v___x_669_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_662_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Name_toStringWithSep(v___x_665_, v_escape_663_, v_n_662_, v_isToken_664_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Name_toStringWithSep(v___x_665_, v___x_668_, v_n_662_, v_isToken_664_);
return v___x_671_;
}
}
else
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Name_toStringWithSep(v___x_665_, v___x_667_, v_n_662_, v_isToken_664_);
return v___x_672_;
}
}
else
{
uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = 0;
v___x_674_ = l_Lean_Name_toStringWithSep(v___x_665_, v___x_673_, v_n_662_, v_isToken_664_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_675_, lean_object* v_escape_676_, lean_object* v_isToken_677_){
_start:
{
uint8_t v_escape_boxed_678_; lean_object* v_res_679_; 
v_escape_boxed_678_ = lean_unbox(v_escape_676_);
v_res_679_ = l_Lean_Name_toStringWithToken(v_n_675_, v_escape_boxed_678_, v_isToken_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_680_, uint8_t v_escape_681_, lean_object* v_n_682_){
_start:
{
switch(lean_obj_tag(v_n_682_))
{
case 0:
{
lean_object* v___x_683_; 
v___x_683_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_683_;
}
case 1:
{
lean_object* v_pre_684_; 
v_pre_684_ = lean_ctor_get(v_n_682_, 0);
if (lean_obj_tag(v_pre_684_) == 0)
{
lean_object* v_str_685_; uint8_t v___x_686_; lean_object* v___x_687_; 
v_str_685_ = lean_ctor_get(v_n_682_, 1);
lean_inc_ref(v_str_685_);
lean_dec_ref_known(v_n_682_, 2);
v___x_686_ = 0;
v___x_687_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_681_, v_str_685_, v___x_686_);
return v___x_687_;
}
else
{
lean_object* v_str_688_; lean_object* v_r_689_; lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v_r_x27_693_; 
lean_inc(v_pre_684_);
v_str_688_ = lean_ctor_get(v_n_682_, 1);
lean_inc_ref(v_str_688_);
lean_dec_ref_known(v_n_682_, 2);
v_r_689_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_680_, v_escape_681_, v_pre_684_);
v___x_690_ = lean_string_append(v_r_689_, v_sep_680_);
v___x_691_ = 0;
v___x_692_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_681_, v_str_688_, v___x_691_);
v_r_x27_693_ = lean_string_append(v___x_690_, v___x_692_);
lean_dec_ref(v___x_692_);
return v_r_x27_693_;
}
}
default: 
{
lean_object* v_pre_694_; 
v_pre_694_ = lean_ctor_get(v_n_682_, 0);
if (lean_obj_tag(v_pre_694_) == 0)
{
lean_object* v_i_695_; lean_object* v___x_696_; 
v_i_695_ = lean_ctor_get(v_n_682_, 1);
lean_inc(v_i_695_);
lean_dec_ref_known(v_n_682_, 2);
v___x_696_ = l_Nat_reprFast(v_i_695_);
return v___x_696_;
}
else
{
lean_object* v_i_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc(v_pre_694_);
v_i_697_ = lean_ctor_get(v_n_682_, 1);
lean_inc(v_i_697_);
lean_dec_ref_known(v_n_682_, 2);
v___x_698_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_680_, v_escape_681_, v_pre_694_);
v___x_699_ = lean_string_append(v___x_698_, v_sep_680_);
v___x_700_ = l_Nat_reprFast(v_i_697_);
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
lean_dec_ref(v___x_700_);
return v___x_701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_702_, lean_object* v_escape_703_, lean_object* v_n_704_){
_start:
{
uint8_t v_escape_boxed_705_; lean_object* v_res_706_; 
v_escape_boxed_705_ = lean_unbox(v_escape_703_);
v_res_706_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_702_, v_escape_boxed_705_, v_n_704_);
lean_dec_ref(v_sep_702_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_707_, uint8_t v_escape_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_708_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_709_, v_escape_708_, v_n_707_);
return v___x_710_;
}
else
{
uint8_t v___x_711_; 
lean_inc(v_n_707_);
v___x_711_ = l_Lean_Name_isInaccessibleUserName(v_n_707_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Name_hasMacroScopes(v_n_707_);
if (v___x_712_ == 0)
{
uint8_t v___x_713_; 
v___x_713_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_707_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_709_, v_escape_708_, v_n_707_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_709_, v___x_712_, v_n_707_);
return v___x_715_;
}
}
else
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_709_, v___x_711_, v_n_707_);
return v___x_716_;
}
}
else
{
uint8_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 0;
v___x_718_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_709_, v___x_717_, v_n_707_);
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_719_, lean_object* v_escape_720_){
_start:
{
uint8_t v_escape_boxed_721_; lean_object* v_res_722_; 
v_escape_boxed_721_ = lean_unbox(v_escape_720_);
v_res_722_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_719_, v_escape_boxed_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_723_, uint8_t v_escape_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_723_, v_escape_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_726_, lean_object* v_escape_727_){
_start:
{
uint8_t v_escape_boxed_728_; lean_object* v_res_729_; 
v_escape_boxed_728_ = lean_unbox(v_escape_727_);
v_res_729_ = l_Lean_Name_toString(v_n_726_, v_escape_boxed_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_730_){
_start:
{
uint8_t v___x_731_; lean_object* v___x_732_; 
v___x_731_ = 1;
v___x_732_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_730_, v___x_731_);
return v___x_732_;
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
