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
lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v_startInclusive_97_; lean_object* v_endExclusive_98_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; uint32_t v___y_124_; uint32_t v___y_129_; uint32_t v___y_135_; lean_object* v___x_151_; uint8_t v_c_152_; uint8_t v___x_161_; uint8_t v___x_162_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v_c_152_ = lean_string_get_byte_fast(v_s_92_, v___x_151_);
v___x_161_ = 97;
v___x_162_ = lean_uint8_dec_le(v___x_161_, v_c_152_);
if (v___x_162_ == 0)
{
goto v___jp_156_;
}
else
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 122;
v___x_164_ = lean_uint8_dec_le(v_c_152_, v___x_163_);
if (v___x_164_ == 0)
{
goto v___jp_156_;
}
else
{
goto v___jp_148_;
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
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_string_utf8_byte_size(v_s_92_);
lean_inc_ref(v_s_92_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v_s_92_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = l_Substring_Raw_nextn(v___x_114_, v___x_115_, v___x_112_);
lean_dec_ref_known(v___x_114_, 3);
v___x_117_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_118_ = l_String_instInhabitedSlice;
v___x_119_ = lean_string_is_valid_pos(v_s_92_, v___x_116_);
if (v___x_119_ == 0)
{
lean_dec(v___x_116_);
lean_dec_ref(v_s_92_);
v___y_104_ = v___x_112_;
v___y_105_ = v___x_117_;
v___y_106_ = v___x_118_;
goto v___jp_103_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = lean_string_is_valid_pos(v_s_92_, v___x_113_);
if (v___x_120_ == 0)
{
lean_dec(v___x_116_);
lean_dec_ref(v_s_92_);
v___y_104_ = v___x_112_;
v___y_105_ = v___x_117_;
v___y_106_ = v___x_118_;
goto v___jp_103_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = lean_nat_dec_le(v___x_116_, v___x_113_);
if (v___x_121_ == 0)
{
lean_dec(v___x_116_);
lean_dec_ref(v_s_92_);
v___y_104_ = v___x_112_;
v___y_105_ = v___x_117_;
v___y_106_ = v___x_118_;
goto v___jp_103_;
}
else
{
lean_object* v___x_122_; 
lean_inc(v___x_116_);
v___x_122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_122_, 0, v_s_92_);
lean_ctor_set(v___x_122_, 1, v___x_116_);
lean_ctor_set(v___x_122_, 2, v___x_113_);
v___y_94_ = v___x_112_;
v___y_95_ = v___x_117_;
v___y_96_ = v___x_122_;
v_startInclusive_97_ = v___x_116_;
v_endExclusive_98_ = v___x_113_;
goto v___jp_93_;
}
}
}
}
v___jp_123_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 95;
v___x_126_ = lean_uint32_dec_eq(v___y_124_, v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = l_Lean_isLetterLike(v___y_124_);
if (v___x_127_ == 0)
{
lean_dec_ref(v_s_92_);
return v___x_127_;
}
else
{
goto v___jp_111_;
}
}
else
{
goto v___jp_111_;
}
}
v___jp_128_:
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 97;
v___x_131_ = lean_uint32_dec_le(v___x_130_, v___y_129_);
if (v___x_131_ == 0)
{
v___y_124_ = v___y_129_;
goto v___jp_123_;
}
else
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 122;
v___x_133_ = lean_uint32_dec_le(v___y_129_, v___x_132_);
if (v___x_133_ == 0)
{
v___y_124_ = v___y_129_;
goto v___jp_123_;
}
else
{
goto v___jp_111_;
}
}
}
v___jp_134_:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 65;
v___x_137_ = lean_uint32_dec_le(v___x_136_, v___y_135_);
if (v___x_137_ == 0)
{
v___y_129_ = v___y_135_;
goto v___jp_128_;
}
else
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 90;
v___x_139_ = lean_uint32_dec_le(v___y_135_, v___x_138_);
if (v___x_139_ == 0)
{
v___y_129_ = v___y_135_;
goto v___jp_128_;
}
else
{
goto v___jp_111_;
}
}
}
v___jp_140_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_string_utf8_byte_size(v_s_92_);
lean_inc_ref(v_s_92_);
v___x_143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_143_, 0, v_s_92_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_142_);
v___x_144_ = l_String_Slice_Pos_get_x3f(v___x_143_, v___x_141_);
lean_dec_ref_known(v___x_143_, 3);
if (lean_obj_tag(v___x_144_) == 0)
{
uint32_t v___x_145_; 
v___x_145_ = 65;
v___y_135_ = v___x_145_;
goto v___jp_134_;
}
else
{
lean_object* v_val_146_; uint32_t v___x_147_; 
v_val_146_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_val_146_);
lean_dec_ref_known(v___x_144_, 1);
v___x_147_ = lean_unbox_uint32(v_val_146_);
lean_dec(v_val_146_);
v___y_135_ = v___x_147_;
goto v___jp_134_;
}
}
v___jp_148_:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_92_, v___x_149_);
if (v___x_150_ == 0)
{
goto v___jp_140_;
}
else
{
lean_dec_ref(v_s_92_);
return v___x_150_;
}
}
v___jp_153_:
{
uint8_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 95;
v___x_155_ = lean_uint8_dec_eq(v_c_152_, v___x_154_);
if (v___x_155_ == 0)
{
goto v___jp_140_;
}
else
{
goto v___jp_148_;
}
}
v___jp_156_:
{
uint8_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 65;
v___x_158_ = lean_uint8_dec_le(v___x_157_, v_c_152_);
if (v___x_158_ == 0)
{
goto v___jp_153_;
}
else
{
uint8_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 90;
v___x_160_ = lean_uint8_dec_le(v_c_152_, v___x_159_);
if (v___x_160_ == 0)
{
goto v___jp_153_;
}
else
{
goto v___jp_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_168_, lean_object* v_h_169_){
_start:
{
lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v_startInclusive_174_; lean_object* v_endExclusive_175_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; uint32_t v___y_201_; uint32_t v___y_206_; uint32_t v___y_212_; lean_object* v___x_228_; uint8_t v_c_229_; uint8_t v___x_238_; uint8_t v___x_239_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v_c_229_ = lean_string_get_byte_fast(v_s_168_, v___x_228_);
v___x_238_ = 97;
v___x_239_ = lean_uint8_dec_le(v___x_238_, v_c_229_);
if (v___x_239_ == 0)
{
goto v___jp_233_;
}
else
{
uint8_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 122;
v___x_241_ = lean_uint8_dec_le(v_c_229_, v___x_240_);
if (v___x_241_ == 0)
{
goto v___jp_233_;
}
else
{
goto v___jp_225_;
}
}
v___jp_170_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v_decide_179_; 
lean_inc_ref(v___y_172_);
v___x_176_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_172_);
v___x_177_ = l_String_Slice_Pos_skipWhile___redArg(v___y_173_, v___y_171_, v___x_176_);
lean_dec_ref(v___y_173_);
v___x_178_ = lean_nat_sub(v_endExclusive_175_, v_startInclusive_174_);
lean_dec(v_startInclusive_174_);
lean_dec(v_endExclusive_175_);
v_decide_179_ = lean_nat_dec_eq(v___x_177_, v___x_178_);
lean_dec(v___x_178_);
lean_dec(v___x_177_);
return v_decide_179_;
}
v___jp_180_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_startInclusive_186_; lean_object* v_endExclusive_187_; 
v___x_184_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_185_ = l_panic___redArg(v___y_183_, v___x_184_);
v_startInclusive_186_ = lean_ctor_get(v___x_185_, 1);
lean_inc(v_startInclusive_186_);
v_endExclusive_187_ = lean_ctor_get(v___x_185_, 2);
lean_inc(v_endExclusive_187_);
v___y_171_ = v___y_181_;
v___y_172_ = v___y_182_;
v___y_173_ = v___x_185_;
v_startInclusive_174_ = v_startInclusive_186_;
v_endExclusive_175_ = v_endExclusive_187_;
goto v___jp_170_;
}
v___jp_188_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_string_utf8_byte_size(v_s_168_);
lean_inc_ref(v_s_168_);
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v_s_168_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_190_);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = l_Substring_Raw_nextn(v___x_191_, v___x_192_, v___x_189_);
lean_dec_ref_known(v___x_191_, 3);
v___x_194_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_195_ = l_String_instInhabitedSlice;
v___x_196_ = lean_string_is_valid_pos(v_s_168_, v___x_193_);
if (v___x_196_ == 0)
{
lean_dec(v___x_193_);
lean_dec_ref(v_s_168_);
v___y_181_ = v___x_189_;
v___y_182_ = v___x_194_;
v___y_183_ = v___x_195_;
goto v___jp_180_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = lean_string_is_valid_pos(v_s_168_, v___x_190_);
if (v___x_197_ == 0)
{
lean_dec(v___x_193_);
lean_dec_ref(v_s_168_);
v___y_181_ = v___x_189_;
v___y_182_ = v___x_194_;
v___y_183_ = v___x_195_;
goto v___jp_180_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = lean_nat_dec_le(v___x_193_, v___x_190_);
if (v___x_198_ == 0)
{
lean_dec(v___x_193_);
lean_dec_ref(v_s_168_);
v___y_181_ = v___x_189_;
v___y_182_ = v___x_194_;
v___y_183_ = v___x_195_;
goto v___jp_180_;
}
else
{
lean_object* v___x_199_; 
lean_inc(v___x_193_);
v___x_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_199_, 0, v_s_168_);
lean_ctor_set(v___x_199_, 1, v___x_193_);
lean_ctor_set(v___x_199_, 2, v___x_190_);
v___y_171_ = v___x_189_;
v___y_172_ = v___x_194_;
v___y_173_ = v___x_199_;
v_startInclusive_174_ = v___x_193_;
v_endExclusive_175_ = v___x_190_;
goto v___jp_170_;
}
}
}
}
v___jp_200_:
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 95;
v___x_203_ = lean_uint32_dec_eq(v___y_201_, v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
v___x_204_ = l_Lean_isLetterLike(v___y_201_);
if (v___x_204_ == 0)
{
lean_dec_ref(v_s_168_);
return v___x_204_;
}
else
{
goto v___jp_188_;
}
}
else
{
goto v___jp_188_;
}
}
v___jp_205_:
{
uint32_t v___x_207_; uint8_t v___x_208_; 
v___x_207_ = 97;
v___x_208_ = lean_uint32_dec_le(v___x_207_, v___y_206_);
if (v___x_208_ == 0)
{
v___y_201_ = v___y_206_;
goto v___jp_200_;
}
else
{
uint32_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 122;
v___x_210_ = lean_uint32_dec_le(v___y_206_, v___x_209_);
if (v___x_210_ == 0)
{
v___y_201_ = v___y_206_;
goto v___jp_200_;
}
else
{
goto v___jp_188_;
}
}
}
v___jp_211_:
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 65;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v___y_212_);
if (v___x_214_ == 0)
{
v___y_206_ = v___y_212_;
goto v___jp_205_;
}
else
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 90;
v___x_216_ = lean_uint32_dec_le(v___y_212_, v___x_215_);
if (v___x_216_ == 0)
{
v___y_206_ = v___y_212_;
goto v___jp_205_;
}
else
{
goto v___jp_188_;
}
}
}
v___jp_217_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_string_utf8_byte_size(v_s_168_);
lean_inc_ref(v_s_168_);
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v_s_168_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = l_String_Slice_Pos_get_x3f(v___x_220_, v___x_218_);
lean_dec_ref_known(v___x_220_, 3);
if (lean_obj_tag(v___x_221_) == 0)
{
uint32_t v___x_222_; 
v___x_222_ = 65;
v___y_212_ = v___x_222_;
goto v___jp_211_;
}
else
{
lean_object* v_val_223_; uint32_t v___x_224_; 
v_val_223_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_221_, 1);
v___x_224_ = lean_unbox_uint32(v_val_223_);
lean_dec(v_val_223_);
v___y_212_ = v___x_224_;
goto v___jp_211_;
}
}
v___jp_225_:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_168_, v___x_226_);
if (v___x_227_ == 0)
{
goto v___jp_217_;
}
else
{
lean_dec_ref(v_s_168_);
return v___x_227_;
}
}
v___jp_230_:
{
uint8_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 95;
v___x_232_ = lean_uint8_dec_eq(v_c_229_, v___x_231_);
if (v___x_232_ == 0)
{
goto v___jp_217_;
}
else
{
goto v___jp_225_;
}
}
v___jp_233_:
{
uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 65;
v___x_235_ = lean_uint8_dec_le(v___x_234_, v_c_229_);
if (v___x_235_ == 0)
{
goto v___jp_230_;
}
else
{
uint8_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 90;
v___x_237_ = lean_uint8_dec_le(v_c_229_, v___x_236_);
if (v___x_237_ == 0)
{
goto v___jp_230_;
}
else
{
goto v___jp_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_242_, lean_object* v_h_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_242_, v_h_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = l_Lean_idBeginEscape;
v___x_248_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_249_ = lean_string_push(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = l_Lean_idEndEscape;
v___x_251_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_252_ = lean_string_push(v___x_251_, v___x_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_255_ = lean_string_append(v___x_254_, v_s_253_);
v___x_256_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_257_ = lean_string_append(v___x_255_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_258_);
lean_dec_ref(v_s_258_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_262_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_271_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_263_, v___x_270_, v___y_264_, lean_box(0), lean_box(0), v___y_267_, v___y_268_, v___y_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_275_, uint8_t v_force_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_string_utf8_byte_size(v_s_275_);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_281_ = lean_string_append(v___x_280_, v_s_275_);
lean_dec_ref(v_s_275_);
v___x_282_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___f_285_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v_startInclusive_300_; lean_object* v_endExclusive_301_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; uint32_t v___y_326_; uint32_t v___y_331_; uint32_t v___y_337_; 
v___f_285_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_276_ == 0)
{
uint8_t v_c_352_; uint8_t v___x_361_; uint8_t v___x_362_; 
v_c_352_ = lean_string_get_byte_fast(v_s_275_, v___x_277_);
v___x_361_ = 97;
v___x_362_ = lean_uint8_dec_le(v___x_361_, v_c_352_);
if (v___x_362_ == 0)
{
goto v___jp_356_;
}
else
{
uint8_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 122;
v___x_364_ = lean_uint8_dec_le(v_c_352_, v___x_363_);
if (v___x_364_ == 0)
{
goto v___jp_356_;
}
else
{
goto v___jp_348_;
}
}
v___jp_353_:
{
uint8_t v___x_354_; uint8_t v___x_355_; 
v___x_354_ = 95;
v___x_355_ = lean_uint8_dec_eq(v_c_352_, v___x_354_);
if (v___x_355_ == 0)
{
goto v___jp_342_;
}
else
{
goto v___jp_348_;
}
}
v___jp_356_:
{
uint8_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 65;
v___x_358_ = lean_uint8_dec_le(v___x_357_, v_c_352_);
if (v___x_358_ == 0)
{
goto v___jp_353_;
}
else
{
uint8_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 90;
v___x_360_ = lean_uint8_dec_le(v_c_352_, v___x_359_);
if (v___x_360_ == 0)
{
goto v___jp_353_;
}
else
{
goto v___jp_348_;
}
}
}
}
else
{
goto v___jp_286_;
}
v___jp_286_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_275_);
v___x_288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_288_, 0, v_s_275_);
lean_ctor_set(v___x_288_, 1, v___x_277_);
lean_ctor_set(v___x_288_, 2, v___x_278_);
v___x_289_ = l_String_Slice_contains___redArg(v___f_285_, v___x_288_, v___x_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_290_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_291_ = lean_string_append(v___x_290_, v_s_275_);
lean_dec_ref(v_s_275_);
v___x_292_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; 
lean_dec_ref(v_s_275_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
v___jp_296_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v_decide_305_; 
lean_inc_ref(v___y_298_);
v___x_302_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_298_);
v___x_303_ = l_String_Slice_Pos_skipWhile___redArg(v___y_299_, v___y_297_, v___x_302_);
lean_dec_ref(v___y_299_);
v___x_304_ = lean_nat_sub(v_endExclusive_301_, v_startInclusive_300_);
lean_dec(v_startInclusive_300_);
lean_dec(v_endExclusive_301_);
v_decide_305_ = lean_nat_dec_eq(v___x_303_, v___x_304_);
lean_dec(v___x_304_);
lean_dec(v___x_303_);
if (v_decide_305_ == 0)
{
goto v___jp_286_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_s_275_);
return v___x_306_;
}
}
v___jp_307_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_startInclusive_313_; lean_object* v_endExclusive_314_; 
v___x_311_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_312_ = l_panic___redArg(v___y_308_, v___x_311_);
v_startInclusive_313_ = lean_ctor_get(v___x_312_, 1);
lean_inc(v_startInclusive_313_);
v_endExclusive_314_ = lean_ctor_get(v___x_312_, 2);
lean_inc(v_endExclusive_314_);
v___y_297_ = v___y_309_;
v___y_298_ = v___y_310_;
v___y_299_ = v___x_312_;
v_startInclusive_300_ = v_startInclusive_313_;
v_endExclusive_301_ = v_endExclusive_314_;
goto v___jp_296_;
}
v___jp_315_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
lean_inc_ref(v_s_275_);
v___x_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_316_, 0, v_s_275_);
lean_ctor_set(v___x_316_, 1, v___x_277_);
lean_ctor_set(v___x_316_, 2, v___x_278_);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = l_Substring_Raw_nextn(v___x_316_, v___x_317_, v___x_277_);
lean_dec_ref_known(v___x_316_, 3);
v___x_319_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_320_ = l_String_instInhabitedSlice;
v___x_321_ = lean_string_is_valid_pos(v_s_275_, v___x_318_);
if (v___x_321_ == 0)
{
lean_dec(v___x_318_);
v___y_308_ = v___x_320_;
v___y_309_ = v___x_277_;
v___y_310_ = v___x_319_;
goto v___jp_307_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = lean_string_is_valid_pos(v_s_275_, v___x_278_);
if (v___x_322_ == 0)
{
lean_dec(v___x_318_);
v___y_308_ = v___x_320_;
v___y_309_ = v___x_277_;
v___y_310_ = v___x_319_;
goto v___jp_307_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_le(v___x_318_, v___x_278_);
if (v___x_323_ == 0)
{
lean_dec(v___x_318_);
v___y_308_ = v___x_320_;
v___y_309_ = v___x_277_;
v___y_310_ = v___x_319_;
goto v___jp_307_;
}
else
{
lean_object* v___x_324_; 
lean_inc(v___x_318_);
lean_inc_ref(v_s_275_);
v___x_324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_324_, 0, v_s_275_);
lean_ctor_set(v___x_324_, 1, v___x_318_);
lean_ctor_set(v___x_324_, 2, v___x_278_);
v___y_297_ = v___x_277_;
v___y_298_ = v___x_319_;
v___y_299_ = v___x_324_;
v_startInclusive_300_ = v___x_318_;
v_endExclusive_301_ = v___x_278_;
goto v___jp_296_;
}
}
}
}
v___jp_325_:
{
uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 95;
v___x_328_ = lean_uint32_dec_eq(v___y_326_, v___x_327_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_isLetterLike(v___y_326_);
if (v___x_329_ == 0)
{
goto v___jp_286_;
}
else
{
goto v___jp_315_;
}
}
else
{
goto v___jp_315_;
}
}
v___jp_330_:
{
uint32_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 97;
v___x_333_ = lean_uint32_dec_le(v___x_332_, v___y_331_);
if (v___x_333_ == 0)
{
v___y_326_ = v___y_331_;
goto v___jp_325_;
}
else
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 122;
v___x_335_ = lean_uint32_dec_le(v___y_331_, v___x_334_);
if (v___x_335_ == 0)
{
v___y_326_ = v___y_331_;
goto v___jp_325_;
}
else
{
goto v___jp_315_;
}
}
}
v___jp_336_:
{
uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 65;
v___x_339_ = lean_uint32_dec_le(v___x_338_, v___y_337_);
if (v___x_339_ == 0)
{
v___y_331_ = v___y_337_;
goto v___jp_330_;
}
else
{
uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 90;
v___x_341_ = lean_uint32_dec_le(v___y_337_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_331_ = v___y_337_;
goto v___jp_330_;
}
else
{
goto v___jp_315_;
}
}
}
v___jp_342_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_inc_ref(v_s_275_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_s_275_);
lean_ctor_set(v___x_343_, 1, v___x_277_);
lean_ctor_set(v___x_343_, 2, v___x_278_);
v___x_344_ = l_String_Slice_Pos_get_x3f(v___x_343_, v___x_277_);
lean_dec_ref_known(v___x_343_, 3);
if (lean_obj_tag(v___x_344_) == 0)
{
uint32_t v___x_345_; 
v___x_345_ = 65;
v___y_337_ = v___x_345_;
goto v___jp_336_;
}
else
{
lean_object* v_val_346_; uint32_t v___x_347_; 
v_val_346_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___x_344_, 1);
v___x_347_ = lean_unbox_uint32(v_val_346_);
lean_dec(v_val_346_);
v___y_337_ = v___x_347_;
goto v___jp_336_;
}
}
v___jp_348_:
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_275_, v___x_349_);
if (v___x_350_ == 0)
{
goto v___jp_342_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_s_275_);
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_365_, lean_object* v_force_366_){
_start:
{
uint8_t v_force_boxed_367_; lean_object* v_res_368_; 
v_force_boxed_367_ = lean_unbox(v_force_366_);
v_res_368_ = l_Lean_Name_escapePart(v_s_365_, v_force_boxed_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_String_instInhabitedSlice;
v___x_371_ = lean_panic_fn_borrowed(v___x_370_, v_msg_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_372_, lean_object* v_pos_373_){
_start:
{
lean_object* v_str_374_; lean_object* v_startInclusive_375_; lean_object* v_endExclusive_376_; lean_object* v___x_377_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v_decide_388_; 
v_str_374_ = lean_ctor_get(v_s_372_, 0);
v_startInclusive_375_ = lean_ctor_get(v_s_372_, 1);
v_endExclusive_376_ = lean_ctor_get(v_s_372_, 2);
v___x_377_ = lean_nat_add(v_startInclusive_375_, v_pos_373_);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_nat_sub(v_endExclusive_376_, v___x_377_);
v_decide_388_ = lean_nat_dec_eq(v___x_386_, v___x_387_);
lean_dec(v___x_387_);
if (v_decide_388_ == 0)
{
uint32_t v___x_389_; uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_389_ = lean_string_utf8_get_fast(v_str_374_, v___x_377_);
v___x_411_ = 65;
v___x_412_ = lean_uint32_dec_le(v___x_411_, v___x_389_);
if (v___x_412_ == 0)
{
goto v___jp_406_;
}
else
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 90;
v___x_414_ = lean_uint32_dec_le(v___x_389_, v___x_413_);
if (v___x_414_ == 0)
{
goto v___jp_406_;
}
else
{
goto v___jp_378_;
}
}
v___jp_390_:
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 95;
v___x_392_ = lean_uint32_dec_eq(v___x_389_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 39;
v___x_394_ = lean_uint32_dec_eq(v___x_389_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 33;
v___x_396_ = lean_uint32_dec_eq(v___x_389_, v___x_395_);
if (v___x_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 63;
v___x_398_ = lean_uint32_dec_eq(v___x_389_, v___x_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
v___x_399_ = l_Lean_isLetterLike(v___x_389_);
if (v___x_399_ == 0)
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_isSubScriptAlnum(v___x_389_);
if (v___x_400_ == 0)
{
lean_dec(v___x_377_);
return v_pos_373_;
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
v___jp_401_:
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 48;
v___x_403_ = lean_uint32_dec_le(v___x_402_, v___x_389_);
if (v___x_403_ == 0)
{
goto v___jp_390_;
}
else
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 57;
v___x_405_ = lean_uint32_dec_le(v___x_389_, v___x_404_);
if (v___x_405_ == 0)
{
goto v___jp_390_;
}
else
{
goto v___jp_378_;
}
}
}
v___jp_406_:
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 97;
v___x_408_ = lean_uint32_dec_le(v___x_407_, v___x_389_);
if (v___x_408_ == 0)
{
goto v___jp_401_;
}
else
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 122;
v___x_410_ = lean_uint32_dec_le(v___x_389_, v___x_409_);
if (v___x_410_ == 0)
{
goto v___jp_401_;
}
else
{
goto v___jp_378_;
}
}
}
}
else
{
lean_dec(v___x_377_);
return v_pos_373_;
}
v___jp_378_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_379_ = lean_string_utf8_next_fast(v_str_374_, v___x_377_);
v___x_380_ = lean_nat_sub(v___x_379_, v___x_377_);
lean_dec(v___x_377_);
v___x_381_ = lean_nat_add(v_pos_373_, v___x_380_);
lean_dec(v___x_380_);
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_add(v_pos_373_, v___x_382_);
v___x_384_ = lean_nat_dec_le(v___x_383_, v___x_381_);
lean_dec(v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v___x_381_);
return v_pos_373_;
}
else
{
lean_dec(v_pos_373_);
v_pos_373_ = v___x_381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_415_, lean_object* v_pos_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_415_, v_pos_416_);
lean_dec_ref(v_s_415_);
return v_res_417_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_418_, lean_object* v_a_419_, uint8_t v_b_420_){
_start:
{
lean_object* v_str_421_; lean_object* v_startInclusive_422_; lean_object* v_endExclusive_423_; lean_object* v___x_424_; uint8_t v_decide_425_; 
v_str_421_ = lean_ctor_get(v_s_418_, 0);
v_startInclusive_422_ = lean_ctor_get(v_s_418_, 1);
v_endExclusive_423_ = lean_ctor_get(v_s_418_, 2);
v___x_424_ = lean_nat_sub(v_endExclusive_423_, v_startInclusive_422_);
v_decide_425_ = lean_nat_dec_eq(v_a_419_, v___x_424_);
lean_dec(v___x_424_);
if (v_decide_425_ == 0)
{
lean_object* v___x_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_426_ = lean_nat_add(v_startInclusive_422_, v_a_419_);
lean_dec(v_a_419_);
v___x_427_ = lean_string_utf8_get_fast(v_str_421_, v___x_426_);
v___x_428_ = l_Lean_idEndEscape;
v___x_429_ = lean_uint32_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_string_utf8_next_fast(v_str_421_, v___x_426_);
lean_dec(v___x_426_);
v___x_431_ = lean_nat_sub(v___x_430_, v_startInclusive_422_);
v_a_419_ = v___x_431_;
v_b_420_ = v___x_429_;
goto _start;
}
else
{
lean_dec(v___x_426_);
return v___x_429_;
}
}
else
{
lean_dec(v_a_419_);
return v_b_420_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_433_, lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
uint8_t v_b_boxed_436_; uint8_t v_res_437_; lean_object* v_r_438_; 
v_b_boxed_436_ = lean_unbox(v_b_435_);
v_res_437_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_433_, v_a_434_, v_b_boxed_436_);
lean_dec_ref(v_s_433_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_439_){
_start:
{
lean_object* v_searcher_440_; uint8_t v___x_441_; uint8_t v___x_442_; 
v_searcher_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = 0;
v___x_442_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_439_, v_searcher_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_443_);
lean_dec_ref(v_s_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_446_, lean_object* v_s_447_, uint8_t v_force_448_){
_start:
{
lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v_startInclusive_461_; lean_object* v_endExclusive_462_; lean_object* v___y_467_; uint32_t v___y_483_; uint32_t v___y_488_; uint32_t v___y_494_; 
if (v_escape_446_ == 0)
{
return v_s_447_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_string_utf8_byte_size(v_s_447_);
v___x_512_ = lean_nat_dec_lt(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_514_ = lean_string_append(v___x_513_, v_s_447_);
lean_dec_ref(v_s_447_);
v___x_515_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
return v___x_516_;
}
else
{
if (v_force_448_ == 0)
{
uint8_t v_c_517_; uint8_t v___x_526_; uint8_t v___x_527_; 
v_c_517_ = lean_string_get_byte_fast(v_s_447_, v___x_510_);
v___x_526_ = 97;
v___x_527_ = lean_uint8_dec_le(v___x_526_, v_c_517_);
if (v___x_527_ == 0)
{
goto v___jp_521_;
}
else
{
uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 122;
v___x_529_ = lean_uint8_dec_le(v_c_517_, v___x_528_);
if (v___x_529_ == 0)
{
goto v___jp_521_;
}
else
{
goto v___jp_507_;
}
}
v___jp_518_:
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 95;
v___x_520_ = lean_uint8_dec_eq(v_c_517_, v___x_519_);
if (v___x_520_ == 0)
{
goto v___jp_499_;
}
else
{
goto v___jp_507_;
}
}
v___jp_521_:
{
uint8_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 65;
v___x_523_ = lean_uint8_dec_le(v___x_522_, v_c_517_);
if (v___x_523_ == 0)
{
goto v___jp_518_;
}
else
{
uint8_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 90;
v___x_525_ = lean_uint8_dec_le(v_c_517_, v___x_524_);
if (v___x_525_ == 0)
{
goto v___jp_518_;
}
else
{
goto v___jp_507_;
}
}
}
}
else
{
goto v___jp_449_;
}
}
}
v___jp_449_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_string_utf8_byte_size(v_s_447_);
lean_inc_ref(v_s_447_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v_s_447_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
v___x_453_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_452_);
lean_dec_ref_known(v___x_452_, 3);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_455_ = lean_string_append(v___x_454_, v_s_447_);
lean_dec_ref(v_s_447_);
v___x_456_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
return v___x_457_;
}
else
{
return v_s_447_;
}
}
v___jp_458_:
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v_decide_465_; 
v___x_463_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_460_, v___y_459_);
lean_dec_ref(v___y_460_);
v___x_464_ = lean_nat_sub(v_endExclusive_462_, v_startInclusive_461_);
lean_dec(v_startInclusive_461_);
lean_dec(v_endExclusive_462_);
v_decide_465_ = lean_nat_dec_eq(v___x_463_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_463_);
if (v_decide_465_ == 0)
{
goto v___jp_449_;
}
else
{
return v_s_447_;
}
}
v___jp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_startInclusive_470_; lean_object* v_endExclusive_471_; 
v___x_468_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_469_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_468_);
v_startInclusive_470_ = lean_ctor_get(v___x_469_, 1);
lean_inc(v_startInclusive_470_);
v_endExclusive_471_ = lean_ctor_get(v___x_469_, 2);
lean_inc(v_endExclusive_471_);
v___y_459_ = v___y_467_;
v___y_460_ = v___x_469_;
v_startInclusive_461_ = v_startInclusive_470_;
v_endExclusive_462_ = v_endExclusive_471_;
goto v___jp_458_;
}
v___jp_472_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_string_utf8_byte_size(v_s_447_);
lean_inc_ref(v_s_447_);
v___x_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_475_, 0, v_s_447_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
lean_ctor_set(v___x_475_, 2, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = l_Substring_Raw_nextn(v___x_475_, v___x_476_, v___x_473_);
lean_dec_ref_known(v___x_475_, 3);
v___x_478_ = lean_string_is_valid_pos(v_s_447_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v___x_477_);
v___y_467_ = v___x_473_;
goto v___jp_466_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = lean_string_is_valid_pos(v_s_447_, v___x_474_);
if (v___x_479_ == 0)
{
lean_dec(v___x_477_);
v___y_467_ = v___x_473_;
goto v___jp_466_;
}
else
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_le(v___x_477_, v___x_474_);
if (v___x_480_ == 0)
{
lean_dec(v___x_477_);
v___y_467_ = v___x_473_;
goto v___jp_466_;
}
else
{
lean_object* v___x_481_; 
lean_inc(v___x_477_);
lean_inc_ref(v_s_447_);
v___x_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_481_, 0, v_s_447_);
lean_ctor_set(v___x_481_, 1, v___x_477_);
lean_ctor_set(v___x_481_, 2, v___x_474_);
v___y_459_ = v___x_473_;
v___y_460_ = v___x_481_;
v_startInclusive_461_ = v___x_477_;
v_endExclusive_462_ = v___x_474_;
goto v___jp_458_;
}
}
}
}
v___jp_482_:
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 95;
v___x_485_ = lean_uint32_dec_eq(v___y_483_, v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = l_Lean_isLetterLike(v___y_483_);
if (v___x_486_ == 0)
{
goto v___jp_449_;
}
else
{
goto v___jp_472_;
}
}
else
{
goto v___jp_472_;
}
}
v___jp_487_:
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 97;
v___x_490_ = lean_uint32_dec_le(v___x_489_, v___y_488_);
if (v___x_490_ == 0)
{
v___y_483_ = v___y_488_;
goto v___jp_482_;
}
else
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 122;
v___x_492_ = lean_uint32_dec_le(v___y_488_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_483_ = v___y_488_;
goto v___jp_482_;
}
else
{
goto v___jp_472_;
}
}
}
v___jp_493_:
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 65;
v___x_496_ = lean_uint32_dec_le(v___x_495_, v___y_494_);
if (v___x_496_ == 0)
{
v___y_488_ = v___y_494_;
goto v___jp_487_;
}
else
{
uint32_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = 90;
v___x_498_ = lean_uint32_dec_le(v___y_494_, v___x_497_);
if (v___x_498_ == 0)
{
v___y_488_ = v___y_494_;
goto v___jp_487_;
}
else
{
goto v___jp_472_;
}
}
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_string_utf8_byte_size(v_s_447_);
lean_inc_ref(v_s_447_);
v___x_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_502_, 0, v_s_447_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
v___x_503_ = l_String_Slice_Pos_get_x3f(v___x_502_, v___x_500_);
lean_dec_ref_known(v___x_502_, 3);
if (lean_obj_tag(v___x_503_) == 0)
{
uint32_t v___x_504_; 
v___x_504_ = 65;
v___y_494_ = v___x_504_;
goto v___jp_493_;
}
else
{
lean_object* v_val_505_; uint32_t v___x_506_; 
v_val_505_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___x_503_, 1);
v___x_506_ = lean_unbox_uint32(v_val_505_);
lean_dec(v_val_505_);
v___y_494_ = v___x_506_;
goto v___jp_493_;
}
}
v___jp_507_:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_447_, v___x_508_);
if (v___x_509_ == 0)
{
goto v___jp_499_;
}
else
{
return v_s_447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_530_, lean_object* v_s_531_, lean_object* v_force_532_){
_start:
{
uint8_t v_escape_boxed_533_; uint8_t v_force_boxed_534_; lean_object* v_res_535_; 
v_escape_boxed_533_ = lean_unbox(v_escape_530_);
v_force_boxed_534_ = lean_unbox(v_force_532_);
v_res_535_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_533_, v_s_531_, v_force_boxed_534_);
return v_res_535_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_536_, lean_object* v_inst_537_, lean_object* v_R_538_, lean_object* v_a_539_, uint8_t v_b_540_, lean_object* v_c_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_536_, v_a_539_, v_b_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v_c_548_){
_start:
{
uint8_t v_b_boxed_549_; uint8_t v_res_550_; lean_object* v_r_551_; 
v_b_boxed_549_ = lean_unbox(v_b_547_);
v_res_550_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_543_, v_inst_544_, v_R_545_, v_a_546_, v_b_boxed_549_, v_c_548_);
lean_dec_ref(v_s_543_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = 0;
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lean_Name_toStringWithSep___lam__0(v_x_554_);
lean_dec_ref(v_x_554_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_559_, uint8_t v_escape_560_, lean_object* v_n_561_, lean_object* v_isToken_562_){
_start:
{
switch(lean_obj_tag(v_n_561_))
{
case 0:
{
lean_object* v___x_563_; 
lean_dec_ref(v_isToken_562_);
v___x_563_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_563_;
}
case 1:
{
lean_object* v_pre_564_; 
v_pre_564_ = lean_ctor_get(v_n_561_, 0);
if (lean_obj_tag(v_pre_564_) == 0)
{
lean_object* v_str_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v_str_565_ = lean_ctor_get(v_n_561_, 1);
lean_inc_ref_n(v_str_565_, 2);
lean_dec_ref_known(v_n_561_, 2);
v___x_566_ = lean_apply_1(v_isToken_562_, v_str_565_);
v___x_567_ = lean_unbox(v___x_566_);
v___x_568_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_560_, v_str_565_, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v_str_569_; lean_object* v_r_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v_r_x27_574_; 
lean_inc(v_pre_564_);
v_str_569_ = lean_ctor_get(v_n_561_, 1);
lean_inc_ref_n(v_str_569_, 2);
lean_dec_ref_known(v_n_561_, 2);
lean_inc_ref(v_isToken_562_);
v_r_570_ = l_Lean_Name_toStringWithSep(v_sep_559_, v_escape_560_, v_pre_564_, v_isToken_562_);
v___x_571_ = lean_string_append(v_r_570_, v_sep_559_);
v___x_572_ = 0;
v___x_573_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_560_, v_str_569_, v___x_572_);
lean_inc_ref(v___x_571_);
v_r_x27_574_ = lean_string_append(v___x_571_, v___x_573_);
lean_dec_ref(v___x_573_);
if (v_escape_560_ == 0)
{
lean_dec_ref(v___x_571_);
lean_dec_ref(v_str_569_);
lean_dec_ref(v_isToken_562_);
return v_r_x27_574_;
}
else
{
lean_object* v___x_575_; uint8_t v___x_576_; 
lean_inc_ref(v_r_x27_574_);
v___x_575_ = lean_apply_1(v_isToken_562_, v_r_x27_574_);
v___x_576_ = lean_unbox(v___x_575_);
if (v___x_576_ == 0)
{
lean_dec_ref(v___x_571_);
lean_dec_ref(v_str_569_);
return v_r_x27_574_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_r_x27_574_);
v___x_577_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_560_, v_str_569_, v_escape_560_);
v___x_578_ = lean_string_append(v___x_571_, v___x_577_);
lean_dec_ref(v___x_577_);
return v___x_578_;
}
}
}
}
default: 
{
lean_object* v_pre_579_; 
lean_dec_ref(v_isToken_562_);
v_pre_579_ = lean_ctor_get(v_n_561_, 0);
if (lean_obj_tag(v_pre_579_) == 0)
{
lean_object* v_i_580_; lean_object* v___x_581_; 
v_i_580_ = lean_ctor_get(v_n_561_, 1);
lean_inc(v_i_580_);
lean_dec_ref_known(v_n_561_, 2);
v___x_581_ = l_Nat_reprFast(v_i_580_);
return v___x_581_;
}
else
{
lean_object* v_i_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_inc(v_pre_579_);
v_i_582_ = lean_ctor_get(v_n_561_, 1);
lean_inc(v_i_582_);
lean_dec_ref_known(v_n_561_, 2);
v___f_583_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_584_ = l_Lean_Name_toStringWithSep(v_sep_559_, v_escape_560_, v_pre_579_, v___f_583_);
v___x_585_ = lean_string_append(v___x_584_, v_sep_559_);
v___x_586_ = l_Nat_reprFast(v_i_582_);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
lean_dec_ref(v___x_586_);
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_588_, lean_object* v_escape_589_, lean_object* v_n_590_, lean_object* v_isToken_591_){
_start:
{
uint8_t v_escape_boxed_592_; lean_object* v_res_593_; 
v_escape_boxed_592_ = lean_unbox(v_escape_589_);
v_res_593_ = l_Lean_Name_toStringWithSep(v_sep_588_, v_escape_boxed_592_, v_n_590_, v_isToken_591_);
lean_dec_ref(v_sep_588_);
return v_res_593_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_600_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_601_ = lean_name_eq(v_n_599_, v___x_600_);
v___x_602_ = 1;
if (v___x_601_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Name_getRoot(v_n_599_);
if (lean_obj_tag(v___x_603_) == 1)
{
lean_object* v_str_604_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_str_604_ = lean_ctor_get(v___x_603_, 1);
lean_inc_ref(v_str_604_);
lean_dec_ref_known(v___x_603_, 2);
v___x_612_ = lean_string_utf8_byte_size(v_str_604_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_dec_le(v___x_613_, v___x_612_);
if (v___x_614_ == 0)
{
goto v___jp_605_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_string_memcmp(v_str_604_, v___x_615_, v___x_616_, v___x_616_, v___x_613_);
if (v___x_617_ == 0)
{
goto v___jp_605_;
}
else
{
lean_dec_ref(v_str_604_);
return v___x_602_;
}
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_string_utf8_byte_size(v_str_604_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_dec_le(v___x_607_, v___x_606_);
if (v___x_608_ == 0)
{
lean_dec_ref(v_str_604_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_string_memcmp(v_str_604_, v___x_609_, v___x_610_, v___x_610_, v___x_607_);
lean_dec_ref(v_str_604_);
return v___x_611_;
}
}
}
else
{
lean_dec(v___x_603_);
return v___x_601_;
}
}
else
{
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_618_);
lean_dec(v_n_618_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_622_, uint8_t v_escape_623_, lean_object* v_isToken_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_623_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Name_toStringWithSep(v___x_625_, v_escape_623_, v_n_622_, v_isToken_624_);
return v___x_626_;
}
else
{
uint8_t v___x_627_; 
lean_inc(v_n_622_);
v___x_627_ = l_Lean_Name_isInaccessibleUserName(v_n_622_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
v___x_628_ = l_Lean_Name_hasMacroScopes(v_n_622_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; 
v___x_629_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_622_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Name_toStringWithSep(v___x_625_, v_escape_623_, v_n_622_, v_isToken_624_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Name_toStringWithSep(v___x_625_, v___x_628_, v_n_622_, v_isToken_624_);
return v___x_631_;
}
}
else
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Name_toStringWithSep(v___x_625_, v___x_627_, v_n_622_, v_isToken_624_);
return v___x_632_;
}
}
else
{
uint8_t v___x_633_; lean_object* v___x_634_; 
v___x_633_ = 0;
v___x_634_ = l_Lean_Name_toStringWithSep(v___x_625_, v___x_633_, v_n_622_, v_isToken_624_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_635_, lean_object* v_escape_636_, lean_object* v_isToken_637_){
_start:
{
uint8_t v_escape_boxed_638_; lean_object* v_res_639_; 
v_escape_boxed_638_ = lean_unbox(v_escape_636_);
v_res_639_ = l_Lean_Name_toStringWithToken(v_n_635_, v_escape_boxed_638_, v_isToken_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_640_, uint8_t v_escape_641_, lean_object* v_n_642_){
_start:
{
switch(lean_obj_tag(v_n_642_))
{
case 0:
{
lean_object* v___x_643_; 
v___x_643_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_643_;
}
case 1:
{
lean_object* v_pre_644_; 
v_pre_644_ = lean_ctor_get(v_n_642_, 0);
if (lean_obj_tag(v_pre_644_) == 0)
{
lean_object* v_str_645_; uint8_t v___x_646_; lean_object* v___x_647_; 
v_str_645_ = lean_ctor_get(v_n_642_, 1);
lean_inc_ref(v_str_645_);
lean_dec_ref_known(v_n_642_, 2);
v___x_646_ = 0;
v___x_647_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_641_, v_str_645_, v___x_646_);
return v___x_647_;
}
else
{
lean_object* v_str_648_; lean_object* v_r_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v_r_x27_653_; 
lean_inc(v_pre_644_);
v_str_648_ = lean_ctor_get(v_n_642_, 1);
lean_inc_ref(v_str_648_);
lean_dec_ref_known(v_n_642_, 2);
v_r_649_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_640_, v_escape_641_, v_pre_644_);
v___x_650_ = lean_string_append(v_r_649_, v_sep_640_);
v___x_651_ = 0;
v___x_652_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_641_, v_str_648_, v___x_651_);
v_r_x27_653_ = lean_string_append(v___x_650_, v___x_652_);
lean_dec_ref(v___x_652_);
return v_r_x27_653_;
}
}
default: 
{
lean_object* v_pre_654_; 
v_pre_654_ = lean_ctor_get(v_n_642_, 0);
if (lean_obj_tag(v_pre_654_) == 0)
{
lean_object* v_i_655_; lean_object* v___x_656_; 
v_i_655_ = lean_ctor_get(v_n_642_, 1);
lean_inc(v_i_655_);
lean_dec_ref_known(v_n_642_, 2);
v___x_656_ = l_Nat_reprFast(v_i_655_);
return v___x_656_;
}
else
{
lean_object* v_i_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_inc(v_pre_654_);
v_i_657_ = lean_ctor_get(v_n_642_, 1);
lean_inc(v_i_657_);
lean_dec_ref_known(v_n_642_, 2);
v___x_658_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_640_, v_escape_641_, v_pre_654_);
v___x_659_ = lean_string_append(v___x_658_, v_sep_640_);
v___x_660_ = l_Nat_reprFast(v_i_657_);
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
lean_dec_ref(v___x_660_);
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_662_, lean_object* v_escape_663_, lean_object* v_n_664_){
_start:
{
uint8_t v_escape_boxed_665_; lean_object* v_res_666_; 
v_escape_boxed_665_ = lean_unbox(v_escape_663_);
v_res_666_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_662_, v_escape_boxed_665_, v_n_664_);
lean_dec_ref(v_sep_662_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_667_, uint8_t v_escape_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_668_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_669_, v_escape_668_, v_n_667_);
return v___x_670_;
}
else
{
uint8_t v___x_671_; 
lean_inc(v_n_667_);
v___x_671_ = l_Lean_Name_isInaccessibleUserName(v_n_667_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
v___x_672_ = l_Lean_Name_hasMacroScopes(v_n_667_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_667_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_669_, v_escape_668_, v_n_667_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_669_, v___x_672_, v_n_667_);
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_669_, v___x_671_, v_n_667_);
return v___x_676_;
}
}
else
{
uint8_t v___x_677_; lean_object* v___x_678_; 
v___x_677_ = 0;
v___x_678_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_669_, v___x_677_, v_n_667_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_679_, lean_object* v_escape_680_){
_start:
{
uint8_t v_escape_boxed_681_; lean_object* v_res_682_; 
v_escape_boxed_681_ = lean_unbox(v_escape_680_);
v_res_682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_679_, v_escape_boxed_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_683_, uint8_t v_escape_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_683_, v_escape_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_686_, lean_object* v_escape_687_){
_start:
{
uint8_t v_escape_boxed_688_; lean_object* v_res_689_; 
v_escape_boxed_688_ = lean_unbox(v_escape_687_);
v_res_689_ = l_Lean_Name_toString(v_n_686_, v_escape_boxed_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_690_){
_start:
{
uint8_t v___x_691_; lean_object* v___x_692_; 
v___x_691_ = 1;
v___x_692_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_690_, v___x_691_);
return v___x_692_;
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
