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
uint8_t lean_uint32_to_uint8(uint32_t);
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
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9;
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
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3;
static const lean_string_object l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4 = (const lean_object*)&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4_value;
static lean_once_cell_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5;
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
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0(void){
_start:
{
uint32_t v___x_1_; uint8_t v___x_2_; 
v___x_1_ = 95;
v___x_2_ = lean_uint32_to_uint8(v___x_1_);
return v___x_2_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1(void){
_start:
{
uint32_t v___x_3_; uint8_t v___x_4_; 
v___x_3_ = 39;
v___x_4_ = lean_uint32_to_uint8(v___x_3_);
return v___x_4_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2(void){
_start:
{
uint32_t v___x_5_; uint8_t v___x_6_; 
v___x_5_ = 33;
v___x_6_ = lean_uint32_to_uint8(v___x_5_);
return v___x_6_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3(void){
_start:
{
uint32_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = 63;
v___x_8_ = lean_uint32_to_uint8(v___x_7_);
return v___x_8_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4(void){
_start:
{
uint32_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = 48;
v___x_10_ = lean_uint32_to_uint8(v___x_9_);
return v___x_10_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5(void){
_start:
{
uint32_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 57;
v___x_12_ = lean_uint32_to_uint8(v___x_11_);
return v___x_12_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6(void){
_start:
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 65;
v___x_14_ = lean_uint32_to_uint8(v___x_13_);
return v___x_14_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7(void){
_start:
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 90;
v___x_16_ = lean_uint32_to_uint8(v___x_15_);
return v___x_16_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8(void){
_start:
{
uint32_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = 97;
v___x_18_ = lean_uint32_to_uint8(v___x_17_);
return v___x_18_;
}
}
static uint8_t _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9(void){
_start:
{
uint32_t v___x_19_; uint8_t v___x_20_; 
v___x_19_ = 122;
v___x_20_ = lean_uint32_to_uint8(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_21_, lean_object* v_i_22_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_string_utf8_byte_size(v_s_21_);
v___x_28_ = lean_nat_dec_lt(v_i_22_, v___x_27_);
if (v___x_28_ == 0)
{
uint8_t v___x_29_; 
lean_dec(v_i_22_);
v___x_29_ = 1;
return v___x_29_;
}
else
{
uint8_t v_c_30_; uint8_t v___x_50_; uint8_t v___x_51_; 
lean_inc(v_i_22_);
v_c_30_ = lean_string_get_byte_fast(v_s_21_, v_i_22_);
v___x_50_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_51_ = lean_uint8_dec_le(v___x_50_, v_c_30_);
if (v___x_51_ == 0)
{
goto v___jp_45_;
}
else
{
uint8_t v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_53_ = lean_uint8_dec_le(v_c_30_, v___x_52_);
if (v___x_53_ == 0)
{
goto v___jp_45_;
}
else
{
goto v___jp_23_;
}
}
v___jp_31_:
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_33_ = lean_uint8_dec_eq(v_c_30_, v___x_32_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1);
v___x_35_ = lean_uint8_dec_eq(v_c_30_, v___x_34_);
if (v___x_35_ == 0)
{
uint8_t v___x_36_; uint8_t v___x_37_; 
v___x_36_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2);
v___x_37_ = lean_uint8_dec_eq(v_c_30_, v___x_36_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3);
v___x_39_ = lean_uint8_dec_eq(v_c_30_, v___x_38_);
if (v___x_39_ == 0)
{
lean_dec(v_i_22_);
return v___x_39_;
}
else
{
goto v___jp_23_;
}
}
else
{
goto v___jp_23_;
}
}
else
{
goto v___jp_23_;
}
}
else
{
goto v___jp_23_;
}
}
v___jp_40_:
{
uint8_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4);
v___x_42_ = lean_uint8_dec_le(v___x_41_, v_c_30_);
if (v___x_42_ == 0)
{
goto v___jp_31_;
}
else
{
uint8_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5);
v___x_44_ = lean_uint8_dec_le(v_c_30_, v___x_43_);
if (v___x_44_ == 0)
{
goto v___jp_31_;
}
else
{
goto v___jp_23_;
}
}
}
v___jp_45_:
{
uint8_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_47_ = lean_uint8_dec_le(v___x_46_, v_c_30_);
if (v___x_47_ == 0)
{
goto v___jp_40_;
}
else
{
uint8_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_49_ = lean_uint8_dec_le(v_c_30_, v___x_48_);
if (v___x_49_ == 0)
{
goto v___jp_40_;
}
else
{
goto v___jp_23_;
}
}
}
}
v___jp_23_:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_add(v_i_22_, v___x_24_);
lean_dec(v_i_22_);
v_i_22_ = v___x_25_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_54_, lean_object* v_i_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_54_, v_i_55_);
lean_dec_ref(v_s_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_58_){
_start:
{
lean_object* v___x_62_; uint8_t v_c_63_; uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v_c_63_ = lean_string_get_byte_fast(v_s_58_, v___x_62_);
v___x_72_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_73_ = lean_uint8_dec_le(v___x_72_, v_c_63_);
if (v___x_73_ == 0)
{
goto v___jp_67_;
}
else
{
uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_75_ = lean_uint8_dec_le(v_c_63_, v___x_74_);
if (v___x_75_ == 0)
{
goto v___jp_67_;
}
else
{
goto v___jp_59_;
}
}
v___jp_59_:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_58_, v___x_60_);
return v___x_61_;
}
v___jp_64_:
{
uint8_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_66_ = lean_uint8_dec_eq(v_c_63_, v___x_65_);
if (v___x_66_ == 0)
{
return v___x_66_;
}
else
{
goto v___jp_59_;
}
}
v___jp_67_:
{
uint8_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_69_ = lean_uint8_dec_le(v___x_68_, v_c_63_);
if (v___x_69_ == 0)
{
goto v___jp_64_;
}
else
{
uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_71_ = lean_uint8_dec_le(v_c_63_, v___x_70_);
if (v___x_71_ == 0)
{
goto v___jp_64_;
}
else
{
goto v___jp_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_76_);
lean_dec_ref(v_s_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_79_, lean_object* v_h_80_){
_start:
{
lean_object* v___x_84_; uint8_t v_c_85_; uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v_c_85_ = lean_string_get_byte_fast(v_s_79_, v___x_84_);
v___x_94_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_95_ = lean_uint8_dec_le(v___x_94_, v_c_85_);
if (v___x_95_ == 0)
{
goto v___jp_89_;
}
else
{
uint8_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_97_ = lean_uint8_dec_le(v_c_85_, v___x_96_);
if (v___x_97_ == 0)
{
goto v___jp_89_;
}
else
{
goto v___jp_81_;
}
}
v___jp_81_:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_79_, v___x_82_);
return v___x_83_;
}
v___jp_86_:
{
uint8_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_88_ = lean_uint8_dec_eq(v_c_85_, v___x_87_);
if (v___x_88_ == 0)
{
return v___x_88_;
}
else
{
goto v___jp_81_;
}
}
v___jp_89_:
{
uint8_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_91_ = lean_uint8_dec_le(v___x_90_, v_c_85_);
if (v___x_91_ == 0)
{
goto v___jp_86_;
}
else
{
uint8_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_93_ = lean_uint8_dec_le(v_c_85_, v___x_92_);
if (v___x_93_ == 0)
{
goto v___jp_86_;
}
else
{
goto v___jp_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_98_, lean_object* v_h_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(v_s_98_, v_h_99_);
lean_dec_ref(v_s_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_105_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2));
v___x_106_ = lean_unsigned_to_nat(14u);
v___x_107_ = lean_unsigned_to_nat(22u);
v___x_108_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1));
v___x_109_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_110_ = l_mkPanicMessageWithDecl(v___x_109_, v___x_108_, v___x_107_, v___x_106_, v___x_105_);
return v___x_110_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_112_){
_start:
{
lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v_startInclusive_117_; lean_object* v_endExclusive_118_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; uint8_t v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; uint8_t v___y_138_; uint32_t v___y_152_; uint32_t v___y_157_; uint8_t v___y_158_; uint32_t v___y_164_; lean_object* v___x_180_; uint8_t v_c_181_; uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v_c_181_ = lean_string_get_byte_fast(v_s_112_, v___x_180_);
v___x_190_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_191_ = lean_uint8_dec_le(v___x_190_, v_c_181_);
if (v___x_191_ == 0)
{
goto v___jp_185_;
}
else
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_193_ = lean_uint8_dec_le(v_c_181_, v___x_192_);
if (v___x_193_ == 0)
{
goto v___jp_185_;
}
else
{
goto v___jp_177_;
}
}
v___jp_113_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v_decide_122_; 
lean_inc_ref(v___y_115_);
v___x_119_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_115_);
v___x_120_ = l_String_Slice_Pos_skipWhile___redArg(v___y_116_, v___y_114_, v___x_119_);
lean_dec_ref(v___y_116_);
v___x_121_ = lean_nat_sub(v_endExclusive_118_, v_startInclusive_117_);
lean_dec(v_startInclusive_117_);
lean_dec(v_endExclusive_118_);
v_decide_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
lean_dec(v___x_121_);
lean_dec(v___x_120_);
return v_decide_122_;
}
v___jp_123_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_startInclusive_129_; lean_object* v_endExclusive_130_; 
v___x_127_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_128_ = l_panic___redArg(v___y_126_, v___x_127_);
v_startInclusive_129_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_startInclusive_129_);
v_endExclusive_130_ = lean_ctor_get(v___x_128_, 2);
lean_inc(v_endExclusive_130_);
v___y_114_ = v___y_124_;
v___y_115_ = v___y_125_;
v___y_116_ = v___x_128_;
v_startInclusive_117_ = v_startInclusive_129_;
v_endExclusive_118_ = v_endExclusive_130_;
goto v___jp_113_;
}
v___jp_131_:
{
if (v___y_132_ == 0)
{
lean_dec(v___y_137_);
lean_dec(v___y_134_);
lean_dec_ref(v_s_112_);
v___y_124_ = v___y_133_;
v___y_125_ = v___y_135_;
v___y_126_ = v___y_136_;
goto v___jp_123_;
}
else
{
if (v___y_138_ == 0)
{
lean_dec(v___y_137_);
lean_dec(v___y_134_);
lean_dec_ref(v_s_112_);
v___y_124_ = v___y_133_;
v___y_125_ = v___y_135_;
v___y_126_ = v___y_136_;
goto v___jp_123_;
}
else
{
lean_object* v___x_139_; 
lean_inc(v___y_134_);
lean_inc(v___y_137_);
v___x_139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_139_, 0, v_s_112_);
lean_ctor_set(v___x_139_, 1, v___y_137_);
lean_ctor_set(v___x_139_, 2, v___y_134_);
v___y_114_ = v___y_133_;
v___y_115_ = v___y_135_;
v___y_116_ = v___x_139_;
v_startInclusive_117_ = v___y_137_;
v_endExclusive_118_ = v___y_134_;
goto v___jp_113_;
}
}
}
v___jp_140_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; uint8_t v___x_149_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_string_utf8_byte_size(v_s_112_);
lean_inc_ref(v_s_112_);
v___x_143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_143_, 0, v_s_112_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Substring_Raw_nextn(v___x_143_, v___x_144_, v___x_141_);
lean_dec_ref_known(v___x_143_, 3);
v___x_146_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_147_ = l_String_instInhabitedSlice;
v___x_148_ = lean_string_is_valid_pos(v_s_112_, v___x_145_);
v___x_149_ = lean_string_is_valid_pos(v_s_112_, v___x_142_);
if (v___x_149_ == 0)
{
v___y_132_ = v___x_148_;
v___y_133_ = v___x_141_;
v___y_134_ = v___x_142_;
v___y_135_ = v___x_146_;
v___y_136_ = v___x_147_;
v___y_137_ = v___x_145_;
v___y_138_ = v___x_149_;
goto v___jp_131_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v___x_145_, v___x_142_);
v___y_132_ = v___x_148_;
v___y_133_ = v___x_141_;
v___y_134_ = v___x_142_;
v___y_135_ = v___x_146_;
v___y_136_ = v___x_147_;
v___y_137_ = v___x_145_;
v___y_138_ = v___x_150_;
goto v___jp_131_;
}
}
v___jp_151_:
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 95;
v___x_154_ = lean_uint32_dec_eq(v___y_152_, v___x_153_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_isLetterLike(v___y_152_);
if (v___x_155_ == 0)
{
lean_dec_ref(v_s_112_);
return v___x_155_;
}
else
{
goto v___jp_140_;
}
}
else
{
goto v___jp_140_;
}
}
v___jp_156_:
{
if (v___y_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 97;
v___x_160_ = lean_uint32_dec_le(v___x_159_, v___y_157_);
if (v___x_160_ == 0)
{
v___y_152_ = v___y_157_;
goto v___jp_151_;
}
else
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 122;
v___x_162_ = lean_uint32_dec_le(v___y_157_, v___x_161_);
if (v___x_162_ == 0)
{
v___y_152_ = v___y_157_;
goto v___jp_151_;
}
else
{
goto v___jp_140_;
}
}
}
else
{
goto v___jp_140_;
}
}
v___jp_163_:
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 65;
v___x_166_ = lean_uint32_dec_le(v___x_165_, v___y_164_);
if (v___x_166_ == 0)
{
v___y_157_ = v___y_164_;
v___y_158_ = v___x_166_;
goto v___jp_156_;
}
else
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 90;
v___x_168_ = lean_uint32_dec_le(v___y_164_, v___x_167_);
v___y_157_ = v___y_164_;
v___y_158_ = v___x_168_;
goto v___jp_156_;
}
}
v___jp_169_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_string_utf8_byte_size(v_s_112_);
lean_inc_ref(v_s_112_);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v_s_112_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
v___x_173_ = l_String_Slice_Pos_get_x3f(v___x_172_, v___x_170_);
lean_dec_ref_known(v___x_172_, 3);
if (lean_obj_tag(v___x_173_) == 0)
{
uint32_t v___x_174_; 
v___x_174_ = 65;
v___y_164_ = v___x_174_;
goto v___jp_163_;
}
else
{
lean_object* v_val_175_; uint32_t v___x_176_; 
v_val_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_173_, 1);
v___x_176_ = lean_unbox_uint32(v_val_175_);
lean_dec(v_val_175_);
v___y_164_ = v___x_176_;
goto v___jp_163_;
}
}
v___jp_177_:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_112_, v___x_178_);
if (v___x_179_ == 0)
{
goto v___jp_169_;
}
else
{
lean_dec_ref(v_s_112_);
return v___x_179_;
}
}
v___jp_182_:
{
uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_184_ = lean_uint8_dec_eq(v_c_181_, v___x_183_);
if (v___x_184_ == 0)
{
goto v___jp_169_;
}
else
{
goto v___jp_177_;
}
}
v___jp_185_:
{
uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_187_ = lean_uint8_dec_le(v___x_186_, v_c_181_);
if (v___x_187_ == 0)
{
goto v___jp_182_;
}
else
{
uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_189_ = lean_uint8_dec_le(v_c_181_, v___x_188_);
if (v___x_189_ == 0)
{
goto v___jp_182_;
}
else
{
goto v___jp_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_197_, lean_object* v_h_198_){
_start:
{
lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v_startInclusive_203_; lean_object* v_endExclusive_204_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; uint8_t v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; uint8_t v___y_224_; uint32_t v___y_238_; uint32_t v___y_243_; uint8_t v___y_244_; uint32_t v___y_250_; lean_object* v___x_266_; uint8_t v_c_267_; uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v_c_267_ = lean_string_get_byte_fast(v_s_197_, v___x_266_);
v___x_276_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_277_ = lean_uint8_dec_le(v___x_276_, v_c_267_);
if (v___x_277_ == 0)
{
goto v___jp_271_;
}
else
{
uint8_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_279_ = lean_uint8_dec_le(v_c_267_, v___x_278_);
if (v___x_279_ == 0)
{
goto v___jp_271_;
}
else
{
goto v___jp_263_;
}
}
v___jp_199_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v_decide_208_; 
lean_inc_ref(v___y_201_);
v___x_205_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_201_);
v___x_206_ = l_String_Slice_Pos_skipWhile___redArg(v___y_202_, v___y_200_, v___x_205_);
lean_dec_ref(v___y_202_);
v___x_207_ = lean_nat_sub(v_endExclusive_204_, v_startInclusive_203_);
lean_dec(v_startInclusive_203_);
lean_dec(v_endExclusive_204_);
v_decide_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
lean_dec(v___x_207_);
lean_dec(v___x_206_);
return v_decide_208_;
}
v___jp_209_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_startInclusive_215_; lean_object* v_endExclusive_216_; 
v___x_213_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_214_ = l_panic___redArg(v___y_212_, v___x_213_);
v_startInclusive_215_ = lean_ctor_get(v___x_214_, 1);
lean_inc(v_startInclusive_215_);
v_endExclusive_216_ = lean_ctor_get(v___x_214_, 2);
lean_inc(v_endExclusive_216_);
v___y_200_ = v___y_210_;
v___y_201_ = v___y_211_;
v___y_202_ = v___x_214_;
v_startInclusive_203_ = v_startInclusive_215_;
v_endExclusive_204_ = v_endExclusive_216_;
goto v___jp_199_;
}
v___jp_217_:
{
if (v___y_218_ == 0)
{
lean_dec(v___y_223_);
lean_dec(v___y_220_);
lean_dec_ref(v_s_197_);
v___y_210_ = v___y_219_;
v___y_211_ = v___y_221_;
v___y_212_ = v___y_222_;
goto v___jp_209_;
}
else
{
if (v___y_224_ == 0)
{
lean_dec(v___y_223_);
lean_dec(v___y_220_);
lean_dec_ref(v_s_197_);
v___y_210_ = v___y_219_;
v___y_211_ = v___y_221_;
v___y_212_ = v___y_222_;
goto v___jp_209_;
}
else
{
lean_object* v___x_225_; 
lean_inc(v___y_220_);
lean_inc(v___y_223_);
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v_s_197_);
lean_ctor_set(v___x_225_, 1, v___y_223_);
lean_ctor_set(v___x_225_, 2, v___y_220_);
v___y_200_ = v___y_219_;
v___y_201_ = v___y_221_;
v___y_202_ = v___x_225_;
v_startInclusive_203_ = v___y_223_;
v_endExclusive_204_ = v___y_220_;
goto v___jp_199_;
}
}
}
v___jp_226_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_string_utf8_byte_size(v_s_197_);
lean_inc_ref(v_s_197_);
v___x_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_229_, 0, v_s_197_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = l_Substring_Raw_nextn(v___x_229_, v___x_230_, v___x_227_);
lean_dec_ref_known(v___x_229_, 3);
v___x_232_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_233_ = l_String_instInhabitedSlice;
v___x_234_ = lean_string_is_valid_pos(v_s_197_, v___x_231_);
v___x_235_ = lean_string_is_valid_pos(v_s_197_, v___x_228_);
if (v___x_235_ == 0)
{
v___y_218_ = v___x_234_;
v___y_219_ = v___x_227_;
v___y_220_ = v___x_228_;
v___y_221_ = v___x_232_;
v___y_222_ = v___x_233_;
v___y_223_ = v___x_231_;
v___y_224_ = v___x_235_;
goto v___jp_217_;
}
else
{
uint8_t v___x_236_; 
v___x_236_ = lean_nat_dec_le(v___x_231_, v___x_228_);
v___y_218_ = v___x_234_;
v___y_219_ = v___x_227_;
v___y_220_ = v___x_228_;
v___y_221_ = v___x_232_;
v___y_222_ = v___x_233_;
v___y_223_ = v___x_231_;
v___y_224_ = v___x_236_;
goto v___jp_217_;
}
}
v___jp_237_:
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 95;
v___x_240_ = lean_uint32_dec_eq(v___y_238_, v___x_239_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
v___x_241_ = l_Lean_isLetterLike(v___y_238_);
if (v___x_241_ == 0)
{
lean_dec_ref(v_s_197_);
return v___x_241_;
}
else
{
goto v___jp_226_;
}
}
else
{
goto v___jp_226_;
}
}
v___jp_242_:
{
if (v___y_244_ == 0)
{
uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 97;
v___x_246_ = lean_uint32_dec_le(v___x_245_, v___y_243_);
if (v___x_246_ == 0)
{
v___y_238_ = v___y_243_;
goto v___jp_237_;
}
else
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 122;
v___x_248_ = lean_uint32_dec_le(v___y_243_, v___x_247_);
if (v___x_248_ == 0)
{
v___y_238_ = v___y_243_;
goto v___jp_237_;
}
else
{
goto v___jp_226_;
}
}
}
else
{
goto v___jp_226_;
}
}
v___jp_249_:
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 65;
v___x_252_ = lean_uint32_dec_le(v___x_251_, v___y_250_);
if (v___x_252_ == 0)
{
v___y_243_ = v___y_250_;
v___y_244_ = v___x_252_;
goto v___jp_242_;
}
else
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 90;
v___x_254_ = lean_uint32_dec_le(v___y_250_, v___x_253_);
v___y_243_ = v___y_250_;
v___y_244_ = v___x_254_;
goto v___jp_242_;
}
}
v___jp_255_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_string_utf8_byte_size(v_s_197_);
lean_inc_ref(v_s_197_);
v___x_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_258_, 0, v_s_197_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_257_);
v___x_259_ = l_String_Slice_Pos_get_x3f(v___x_258_, v___x_256_);
lean_dec_ref_known(v___x_258_, 3);
if (lean_obj_tag(v___x_259_) == 0)
{
uint32_t v___x_260_; 
v___x_260_ = 65;
v___y_250_ = v___x_260_;
goto v___jp_249_;
}
else
{
lean_object* v_val_261_; uint32_t v___x_262_; 
v_val_261_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v___x_259_, 1);
v___x_262_ = lean_unbox_uint32(v_val_261_);
lean_dec(v_val_261_);
v___y_250_ = v___x_262_;
goto v___jp_249_;
}
}
v___jp_263_:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_197_, v___x_264_);
if (v___x_265_ == 0)
{
goto v___jp_255_;
}
else
{
lean_dec_ref(v_s_197_);
return v___x_265_;
}
}
v___jp_268_:
{
uint8_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_270_ = lean_uint8_dec_eq(v_c_267_, v___x_269_);
if (v___x_270_ == 0)
{
goto v___jp_255_;
}
else
{
goto v___jp_263_;
}
}
v___jp_271_:
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_273_ = lean_uint8_dec_le(v___x_272_, v_c_267_);
if (v___x_273_ == 0)
{
goto v___jp_268_;
}
else
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_275_ = lean_uint8_dec_le(v_c_267_, v___x_274_);
if (v___x_275_ == 0)
{
goto v___jp_268_;
}
else
{
goto v___jp_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_280_, lean_object* v_h_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_280_, v_h_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_idBeginEscape;
v___x_286_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_287_ = lean_string_push(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = l_Lean_idEndEscape;
v___x_289_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_290_ = lean_string_push(v___x_289_, v___x_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_293_ = lean_string_append(v___x_292_, v_s_291_);
v___x_294_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_296_);
lean_dec_ref(v_s_296_);
return v_res_297_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_300_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_309_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_301_, v___x_308_, v___y_302_, lean_box(0), lean_box(0), v___y_305_, v___y_306_, v___y_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_313_, uint8_t v_force_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_string_utf8_byte_size(v_s_313_);
v___x_317_ = lean_nat_dec_lt(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_318_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_319_ = lean_string_append(v___x_318_, v_s_313_);
lean_dec_ref(v_s_313_);
v___x_320_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
else
{
lean_object* v___f_323_; uint8_t v___y_335_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v_startInclusive_341_; lean_object* v_endExclusive_342_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; uint8_t v___y_360_; lean_object* v___y_361_; uint8_t v___y_362_; uint32_t v___y_374_; uint32_t v___y_379_; uint8_t v___y_380_; uint32_t v___y_386_; 
v___f_323_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_314_ == 0)
{
uint8_t v_c_400_; uint8_t v___x_409_; uint8_t v___x_410_; 
v_c_400_ = lean_string_get_byte_fast(v_s_313_, v___x_315_);
v___x_409_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_410_ = lean_uint8_dec_le(v___x_409_, v_c_400_);
if (v___x_410_ == 0)
{
goto v___jp_404_;
}
else
{
uint8_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_412_ = lean_uint8_dec_le(v_c_400_, v___x_411_);
if (v___x_412_ == 0)
{
goto v___jp_404_;
}
else
{
goto v___jp_397_;
}
}
v___jp_401_:
{
uint8_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_403_ = lean_uint8_dec_eq(v_c_400_, v___x_402_);
if (v___x_403_ == 0)
{
goto v___jp_391_;
}
else
{
goto v___jp_397_;
}
}
v___jp_404_:
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_406_ = lean_uint8_dec_le(v___x_405_, v_c_400_);
if (v___x_406_ == 0)
{
goto v___jp_401_;
}
else
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_408_ = lean_uint8_dec_le(v_c_400_, v___x_407_);
if (v___x_408_ == 0)
{
goto v___jp_401_;
}
else
{
goto v___jp_397_;
}
}
}
}
else
{
goto v___jp_324_;
}
v___jp_324_:
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_325_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_313_);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v_s_313_);
lean_ctor_set(v___x_326_, 1, v___x_315_);
lean_ctor_set(v___x_326_, 2, v___x_316_);
v___x_327_ = l_String_Slice_contains___redArg(v___f_323_, v___x_326_, v___x_325_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_329_ = lean_string_append(v___x_328_, v_s_313_);
lean_dec_ref(v_s_313_);
v___x_330_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; 
lean_dec_ref(v_s_313_);
v___x_333_ = lean_box(0);
return v___x_333_;
}
}
v___jp_334_:
{
if (v___y_335_ == 0)
{
goto v___jp_324_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_s_313_);
return v___x_336_;
}
}
v___jp_337_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v_decide_346_; 
lean_inc_ref(v___y_339_);
v___x_343_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_339_);
v___x_344_ = l_String_Slice_Pos_skipWhile___redArg(v___y_340_, v___y_338_, v___x_343_);
lean_dec_ref(v___y_340_);
v___x_345_ = lean_nat_sub(v_endExclusive_342_, v_startInclusive_341_);
lean_dec(v_startInclusive_341_);
lean_dec(v_endExclusive_342_);
v_decide_346_ = lean_nat_dec_eq(v___x_344_, v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_344_);
v___y_335_ = v_decide_346_;
goto v___jp_334_;
}
v___jp_347_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_startInclusive_353_; lean_object* v_endExclusive_354_; 
v___x_351_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_352_ = l_panic___redArg(v___y_350_, v___x_351_);
v_startInclusive_353_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_startInclusive_353_);
v_endExclusive_354_ = lean_ctor_get(v___x_352_, 2);
lean_inc(v_endExclusive_354_);
v___y_338_ = v___y_348_;
v___y_339_ = v___y_349_;
v___y_340_ = v___x_352_;
v_startInclusive_341_ = v_startInclusive_353_;
v_endExclusive_342_ = v_endExclusive_354_;
goto v___jp_337_;
}
v___jp_355_:
{
if (v___y_360_ == 0)
{
lean_dec(v___y_361_);
lean_dec(v___y_358_);
v___y_348_ = v___y_356_;
v___y_349_ = v___y_357_;
v___y_350_ = v___y_359_;
goto v___jp_347_;
}
else
{
if (v___y_362_ == 0)
{
lean_dec(v___y_361_);
lean_dec(v___y_358_);
v___y_348_ = v___y_356_;
v___y_349_ = v___y_357_;
v___y_350_ = v___y_359_;
goto v___jp_347_;
}
else
{
lean_object* v___x_363_; 
lean_inc(v___y_358_);
lean_inc(v___y_361_);
lean_inc_ref(v_s_313_);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v_s_313_);
lean_ctor_set(v___x_363_, 1, v___y_361_);
lean_ctor_set(v___x_363_, 2, v___y_358_);
v___y_338_ = v___y_356_;
v___y_339_ = v___y_357_;
v___y_340_ = v___x_363_;
v_startInclusive_341_ = v___y_361_;
v_endExclusive_342_ = v___y_358_;
goto v___jp_337_;
}
}
}
v___jp_364_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; 
lean_inc_ref(v_s_313_);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v_s_313_);
lean_ctor_set(v___x_365_, 1, v___x_315_);
lean_ctor_set(v___x_365_, 2, v___x_316_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = l_Substring_Raw_nextn(v___x_365_, v___x_366_, v___x_315_);
lean_dec_ref_known(v___x_365_, 3);
v___x_368_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_369_ = l_String_instInhabitedSlice;
v___x_370_ = lean_string_is_valid_pos(v_s_313_, v___x_367_);
v___x_371_ = lean_string_is_valid_pos(v_s_313_, v___x_316_);
if (v___x_371_ == 0)
{
v___y_356_ = v___x_315_;
v___y_357_ = v___x_368_;
v___y_358_ = v___x_316_;
v___y_359_ = v___x_369_;
v___y_360_ = v___x_370_;
v___y_361_ = v___x_367_;
v___y_362_ = v___x_371_;
goto v___jp_355_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_le(v___x_367_, v___x_316_);
v___y_356_ = v___x_315_;
v___y_357_ = v___x_368_;
v___y_358_ = v___x_316_;
v___y_359_ = v___x_369_;
v___y_360_ = v___x_370_;
v___y_361_ = v___x_367_;
v___y_362_ = v___x_372_;
goto v___jp_355_;
}
}
v___jp_373_:
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 95;
v___x_376_ = lean_uint32_dec_eq(v___y_374_, v___x_375_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_isLetterLike(v___y_374_);
if (v___x_377_ == 0)
{
v___y_335_ = v___x_377_;
goto v___jp_334_;
}
else
{
goto v___jp_364_;
}
}
else
{
goto v___jp_364_;
}
}
v___jp_378_:
{
if (v___y_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 97;
v___x_382_ = lean_uint32_dec_le(v___x_381_, v___y_379_);
if (v___x_382_ == 0)
{
v___y_374_ = v___y_379_;
goto v___jp_373_;
}
else
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 122;
v___x_384_ = lean_uint32_dec_le(v___y_379_, v___x_383_);
if (v___x_384_ == 0)
{
v___y_374_ = v___y_379_;
goto v___jp_373_;
}
else
{
goto v___jp_364_;
}
}
}
else
{
goto v___jp_364_;
}
}
v___jp_385_:
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 65;
v___x_388_ = lean_uint32_dec_le(v___x_387_, v___y_386_);
if (v___x_388_ == 0)
{
v___y_379_ = v___y_386_;
v___y_380_ = v___x_388_;
goto v___jp_378_;
}
else
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 90;
v___x_390_ = lean_uint32_dec_le(v___y_386_, v___x_389_);
v___y_379_ = v___y_386_;
v___y_380_ = v___x_390_;
goto v___jp_378_;
}
}
v___jp_391_:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc_ref(v_s_313_);
v___x_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_392_, 0, v_s_313_);
lean_ctor_set(v___x_392_, 1, v___x_315_);
lean_ctor_set(v___x_392_, 2, v___x_316_);
v___x_393_ = l_String_Slice_Pos_get_x3f(v___x_392_, v___x_315_);
lean_dec_ref_known(v___x_392_, 3);
if (lean_obj_tag(v___x_393_) == 0)
{
uint32_t v___x_394_; 
v___x_394_ = 65;
v___y_386_ = v___x_394_;
goto v___jp_385_;
}
else
{
lean_object* v_val_395_; uint32_t v___x_396_; 
v_val_395_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_393_, 1);
v___x_396_ = lean_unbox_uint32(v_val_395_);
lean_dec(v_val_395_);
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
}
v___jp_397_:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_313_, v___x_398_);
if (v___x_399_ == 0)
{
goto v___jp_391_;
}
else
{
v___y_335_ = v___x_399_;
goto v___jp_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_413_, lean_object* v_force_414_){
_start:
{
uint8_t v_force_boxed_415_; lean_object* v_res_416_; 
v_force_boxed_415_ = lean_unbox(v_force_414_);
v_res_416_ = l_Lean_Name_escapePart(v_s_413_, v_force_boxed_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = l_String_instInhabitedSlice;
v___x_419_ = lean_panic_fn_borrowed(v___x_418_, v_msg_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_420_, lean_object* v_pos_421_){
_start:
{
lean_object* v_str_422_; lean_object* v_startInclusive_423_; lean_object* v_endExclusive_424_; lean_object* v___x_425_; uint8_t v___y_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v_decide_438_; 
v_str_422_ = lean_ctor_get(v_s_420_, 0);
v_startInclusive_423_ = lean_ctor_get(v_s_420_, 1);
v_endExclusive_424_ = lean_ctor_get(v_s_420_, 2);
v___x_425_ = lean_nat_add(v_startInclusive_423_, v_pos_421_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_sub(v_endExclusive_424_, v___x_425_);
v_decide_438_ = lean_nat_dec_eq(v___x_436_, v___x_437_);
lean_dec(v___x_437_);
if (v_decide_438_ == 0)
{
uint32_t v___x_439_; uint8_t v___y_457_; uint32_t v___x_462_; uint8_t v___x_463_; 
v___x_439_ = lean_string_utf8_get_fast(v_str_422_, v___x_425_);
v___x_462_ = 65;
v___x_463_ = lean_uint32_dec_le(v___x_462_, v___x_439_);
if (v___x_463_ == 0)
{
v___y_457_ = v___x_463_;
goto v___jp_456_;
}
else
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 90;
v___x_465_ = lean_uint32_dec_le(v___x_439_, v___x_464_);
v___y_457_ = v___x_465_;
goto v___jp_456_;
}
v___jp_440_:
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 95;
v___x_442_ = lean_uint32_dec_eq(v___x_439_, v___x_441_);
if (v___x_442_ == 0)
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 39;
v___x_444_ = lean_uint32_dec_eq(v___x_439_, v___x_443_);
if (v___x_444_ == 0)
{
uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 33;
v___x_446_ = lean_uint32_dec_eq(v___x_439_, v___x_445_);
if (v___x_446_ == 0)
{
uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 63;
v___x_448_ = lean_uint32_dec_eq(v___x_439_, v___x_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_isLetterLike(v___x_439_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
v___x_450_ = l_Lean_isSubScriptAlnum(v___x_439_);
v___y_435_ = v___x_450_;
goto v___jp_434_;
}
else
{
v___y_435_ = v___x_449_;
goto v___jp_434_;
}
}
else
{
goto v___jp_426_;
}
}
else
{
goto v___jp_426_;
}
}
else
{
goto v___jp_426_;
}
}
else
{
goto v___jp_426_;
}
}
v___jp_451_:
{
uint32_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = 48;
v___x_453_ = lean_uint32_dec_le(v___x_452_, v___x_439_);
if (v___x_453_ == 0)
{
goto v___jp_440_;
}
else
{
uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_454_ = 57;
v___x_455_ = lean_uint32_dec_le(v___x_439_, v___x_454_);
if (v___x_455_ == 0)
{
goto v___jp_440_;
}
else
{
goto v___jp_426_;
}
}
}
v___jp_456_:
{
if (v___y_457_ == 0)
{
uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 97;
v___x_459_ = lean_uint32_dec_le(v___x_458_, v___x_439_);
if (v___x_459_ == 0)
{
goto v___jp_451_;
}
else
{
uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 122;
v___x_461_ = lean_uint32_dec_le(v___x_439_, v___x_460_);
if (v___x_461_ == 0)
{
goto v___jp_451_;
}
else
{
goto v___jp_426_;
}
}
}
else
{
goto v___jp_426_;
}
}
}
else
{
lean_dec(v___x_425_);
return v_pos_421_;
}
v___jp_426_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_427_ = lean_string_utf8_next_fast(v_str_422_, v___x_425_);
v___x_428_ = lean_nat_sub(v___x_427_, v___x_425_);
lean_dec(v___x_425_);
v___x_429_ = lean_nat_add(v_pos_421_, v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_pos_421_, v___x_430_);
v___x_432_ = lean_nat_dec_le(v___x_431_, v___x_429_);
lean_dec(v___x_431_);
if (v___x_432_ == 0)
{
lean_dec(v___x_429_);
return v_pos_421_;
}
else
{
lean_dec(v_pos_421_);
v_pos_421_ = v___x_429_;
goto _start;
}
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
lean_dec(v___x_425_);
return v_pos_421_;
}
else
{
goto v___jp_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_466_, lean_object* v_pos_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_466_, v_pos_467_);
lean_dec_ref(v_s_466_);
return v_res_468_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_469_, lean_object* v_a_470_, uint8_t v_b_471_){
_start:
{
lean_object* v_str_472_; lean_object* v_startInclusive_473_; lean_object* v_endExclusive_474_; lean_object* v___x_475_; uint8_t v_decide_476_; 
v_str_472_ = lean_ctor_get(v_s_469_, 0);
v_startInclusive_473_ = lean_ctor_get(v_s_469_, 1);
v_endExclusive_474_ = lean_ctor_get(v_s_469_, 2);
v___x_475_ = lean_nat_sub(v_endExclusive_474_, v_startInclusive_473_);
v_decide_476_ = lean_nat_dec_eq(v_a_470_, v___x_475_);
lean_dec(v___x_475_);
if (v_decide_476_ == 0)
{
lean_object* v___x_477_; uint32_t v___x_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_477_ = lean_nat_add(v_startInclusive_473_, v_a_470_);
lean_dec(v_a_470_);
v___x_478_ = lean_string_utf8_get_fast(v_str_472_, v___x_477_);
v___x_479_ = 187;
v___x_480_ = lean_uint32_dec_eq(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_string_utf8_next_fast(v_str_472_, v___x_477_);
lean_dec(v___x_477_);
v___x_482_ = lean_nat_sub(v___x_481_, v_startInclusive_473_);
v_a_470_ = v___x_482_;
v_b_471_ = v___x_480_;
goto _start;
}
else
{
lean_dec(v___x_477_);
return v___x_480_;
}
}
else
{
lean_dec(v_a_470_);
return v_b_471_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
uint8_t v_b_boxed_487_; uint8_t v_res_488_; lean_object* v_r_489_; 
v_b_boxed_487_ = lean_unbox(v_b_486_);
v_res_488_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_484_, v_a_485_, v_b_boxed_487_);
lean_dec_ref(v_s_484_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_490_){
_start:
{
lean_object* v_searcher_491_; uint8_t v___x_492_; uint8_t v___x_493_; 
v_searcher_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = 0;
v___x_493_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_490_, v_searcher_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_494_);
lean_dec_ref(v_s_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_497_, lean_object* v_s_498_, uint8_t v_force_499_){
_start:
{
uint8_t v___y_510_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v_startInclusive_514_; lean_object* v_endExclusive_515_; lean_object* v___y_520_; lean_object* v___y_526_; lean_object* v___y_527_; uint8_t v___y_528_; lean_object* v___y_529_; uint8_t v___y_530_; uint32_t v___y_542_; uint32_t v___y_547_; uint8_t v___y_548_; uint32_t v___y_554_; 
if (v_escape_497_ == 0)
{
return v_s_498_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_string_utf8_byte_size(v_s_498_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_574_ = lean_string_append(v___x_573_, v_s_498_);
lean_dec_ref(v_s_498_);
v___x_575_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
return v___x_576_;
}
else
{
if (v_force_499_ == 0)
{
uint8_t v_c_577_; uint8_t v___x_586_; uint8_t v___x_587_; 
v_c_577_ = lean_string_get_byte_fast(v_s_498_, v___x_570_);
v___x_586_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_587_ = lean_uint8_dec_le(v___x_586_, v_c_577_);
if (v___x_587_ == 0)
{
goto v___jp_581_;
}
else
{
uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_589_ = lean_uint8_dec_le(v_c_577_, v___x_588_);
if (v___x_589_ == 0)
{
goto v___jp_581_;
}
else
{
goto v___jp_567_;
}
}
v___jp_578_:
{
uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_580_ = lean_uint8_dec_eq(v_c_577_, v___x_579_);
if (v___x_580_ == 0)
{
goto v___jp_559_;
}
else
{
goto v___jp_567_;
}
}
v___jp_581_:
{
uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_583_ = lean_uint8_dec_le(v___x_582_, v_c_577_);
if (v___x_583_ == 0)
{
goto v___jp_578_;
}
else
{
uint8_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_585_ = lean_uint8_dec_le(v_c_577_, v___x_584_);
if (v___x_585_ == 0)
{
goto v___jp_578_;
}
else
{
goto v___jp_567_;
}
}
}
}
else
{
goto v___jp_500_;
}
}
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_string_utf8_byte_size(v_s_498_);
lean_inc_ref(v_s_498_);
v___x_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_503_, 0, v_s_498_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
v___x_504_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_503_);
lean_dec_ref_known(v___x_503_, 3);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_506_ = lean_string_append(v___x_505_, v_s_498_);
lean_dec_ref(v_s_498_);
v___x_507_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_508_ = lean_string_append(v___x_506_, v___x_507_);
return v___x_508_;
}
else
{
return v_s_498_;
}
}
v___jp_509_:
{
if (v___y_510_ == 0)
{
goto v___jp_500_;
}
else
{
return v_s_498_;
}
}
v___jp_511_:
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v_decide_518_; 
v___x_516_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_513_, v___y_512_);
lean_dec_ref(v___y_513_);
v___x_517_ = lean_nat_sub(v_endExclusive_515_, v_startInclusive_514_);
lean_dec(v_startInclusive_514_);
lean_dec(v_endExclusive_515_);
v_decide_518_ = lean_nat_dec_eq(v___x_516_, v___x_517_);
lean_dec(v___x_517_);
lean_dec(v___x_516_);
v___y_510_ = v_decide_518_;
goto v___jp_509_;
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_startInclusive_523_; lean_object* v_endExclusive_524_; 
v___x_521_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_522_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_521_);
v_startInclusive_523_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_startInclusive_523_);
v_endExclusive_524_ = lean_ctor_get(v___x_522_, 2);
lean_inc(v_endExclusive_524_);
v___y_512_ = v___y_520_;
v___y_513_ = v___x_522_;
v_startInclusive_514_ = v_startInclusive_523_;
v_endExclusive_515_ = v_endExclusive_524_;
goto v___jp_511_;
}
v___jp_525_:
{
if (v___y_528_ == 0)
{
lean_dec(v___y_527_);
lean_dec(v___y_526_);
v___y_520_ = v___y_529_;
goto v___jp_519_;
}
else
{
if (v___y_530_ == 0)
{
lean_dec(v___y_527_);
lean_dec(v___y_526_);
v___y_520_ = v___y_529_;
goto v___jp_519_;
}
else
{
lean_object* v___x_531_; 
lean_inc(v___y_526_);
lean_inc(v___y_527_);
lean_inc_ref(v_s_498_);
v___x_531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_531_, 0, v_s_498_);
lean_ctor_set(v___x_531_, 1, v___y_527_);
lean_ctor_set(v___x_531_, 2, v___y_526_);
v___y_512_ = v___y_529_;
v___y_513_ = v___x_531_;
v_startInclusive_514_ = v___y_527_;
v_endExclusive_515_ = v___y_526_;
goto v___jp_511_;
}
}
}
v___jp_532_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; uint8_t v___x_539_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_string_utf8_byte_size(v_s_498_);
lean_inc_ref(v_s_498_);
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v_s_498_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
lean_ctor_set(v___x_535_, 2, v___x_534_);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = l_Substring_Raw_nextn(v___x_535_, v___x_536_, v___x_533_);
lean_dec_ref_known(v___x_535_, 3);
v___x_538_ = lean_string_is_valid_pos(v_s_498_, v___x_537_);
v___x_539_ = lean_string_is_valid_pos(v_s_498_, v___x_534_);
if (v___x_539_ == 0)
{
v___y_526_ = v___x_534_;
v___y_527_ = v___x_537_;
v___y_528_ = v___x_538_;
v___y_529_ = v___x_533_;
v___y_530_ = v___x_539_;
goto v___jp_525_;
}
else
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_le(v___x_537_, v___x_534_);
v___y_526_ = v___x_534_;
v___y_527_ = v___x_537_;
v___y_528_ = v___x_538_;
v___y_529_ = v___x_533_;
v___y_530_ = v___x_540_;
goto v___jp_525_;
}
}
v___jp_541_:
{
uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = 95;
v___x_544_ = lean_uint32_dec_eq(v___y_542_, v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = l_Lean_isLetterLike(v___y_542_);
if (v___x_545_ == 0)
{
v___y_510_ = v___x_545_;
goto v___jp_509_;
}
else
{
goto v___jp_532_;
}
}
else
{
goto v___jp_532_;
}
}
v___jp_546_:
{
if (v___y_548_ == 0)
{
uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 97;
v___x_550_ = lean_uint32_dec_le(v___x_549_, v___y_547_);
if (v___x_550_ == 0)
{
v___y_542_ = v___y_547_;
goto v___jp_541_;
}
else
{
uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 122;
v___x_552_ = lean_uint32_dec_le(v___y_547_, v___x_551_);
if (v___x_552_ == 0)
{
v___y_542_ = v___y_547_;
goto v___jp_541_;
}
else
{
goto v___jp_532_;
}
}
}
else
{
goto v___jp_532_;
}
}
v___jp_553_:
{
uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 65;
v___x_556_ = lean_uint32_dec_le(v___x_555_, v___y_554_);
if (v___x_556_ == 0)
{
v___y_547_ = v___y_554_;
v___y_548_ = v___x_556_;
goto v___jp_546_;
}
else
{
uint32_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = 90;
v___x_558_ = lean_uint32_dec_le(v___y_554_, v___x_557_);
v___y_547_ = v___y_554_;
v___y_548_ = v___x_558_;
goto v___jp_546_;
}
}
v___jp_559_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_string_utf8_byte_size(v_s_498_);
lean_inc_ref(v_s_498_);
v___x_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_562_, 0, v_s_498_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_561_);
v___x_563_ = l_String_Slice_Pos_get_x3f(v___x_562_, v___x_560_);
lean_dec_ref_known(v___x_562_, 3);
if (lean_obj_tag(v___x_563_) == 0)
{
uint32_t v___x_564_; 
v___x_564_ = 65;
v___y_554_ = v___x_564_;
goto v___jp_553_;
}
else
{
lean_object* v_val_565_; uint32_t v___x_566_; 
v_val_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v___x_563_, 1);
v___x_566_ = lean_unbox_uint32(v_val_565_);
lean_dec(v_val_565_);
v___y_554_ = v___x_566_;
goto v___jp_553_;
}
}
v___jp_567_:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_498_, v___x_568_);
if (v___x_569_ == 0)
{
goto v___jp_559_;
}
else
{
v___y_510_ = v___x_569_;
goto v___jp_509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_590_, lean_object* v_s_591_, lean_object* v_force_592_){
_start:
{
uint8_t v_escape_boxed_593_; uint8_t v_force_boxed_594_; lean_object* v_res_595_; 
v_escape_boxed_593_ = lean_unbox(v_escape_590_);
v_force_boxed_594_ = lean_unbox(v_force_592_);
v_res_595_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_593_, v_s_591_, v_force_boxed_594_);
return v_res_595_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_596_, lean_object* v_inst_597_, lean_object* v_R_598_, lean_object* v_a_599_, uint8_t v_b_600_, lean_object* v_c_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_596_, v_a_599_, v_b_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_603_, lean_object* v_inst_604_, lean_object* v_R_605_, lean_object* v_a_606_, lean_object* v_b_607_, lean_object* v_c_608_){
_start:
{
uint8_t v_b_boxed_609_; uint8_t v_res_610_; lean_object* v_r_611_; 
v_b_boxed_609_ = lean_unbox(v_b_607_);
v_res_610_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_603_, v_inst_604_, v_R_605_, v_a_606_, v_b_boxed_609_, v_c_608_);
lean_dec_ref(v_s_603_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Lean_Name_toStringWithSep___lam__0(v_x_614_);
lean_dec_ref(v_x_614_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_619_, uint8_t v_escape_620_, lean_object* v_n_621_, lean_object* v_isToken_622_){
_start:
{
switch(lean_obj_tag(v_n_621_))
{
case 0:
{
lean_object* v___x_623_; 
lean_dec_ref(v_isToken_622_);
v___x_623_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_623_;
}
case 1:
{
lean_object* v_pre_624_; 
v_pre_624_ = lean_ctor_get(v_n_621_, 0);
if (lean_obj_tag(v_pre_624_) == 0)
{
lean_object* v_str_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; 
v_str_625_ = lean_ctor_get(v_n_621_, 1);
lean_inc_ref_n(v_str_625_, 2);
lean_dec_ref_known(v_n_621_, 2);
v___x_626_ = lean_apply_1(v_isToken_622_, v_str_625_);
v___x_627_ = lean_unbox(v___x_626_);
v___x_628_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_620_, v_str_625_, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v_str_629_; lean_object* v_r_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v_r_x27_634_; 
lean_inc(v_pre_624_);
v_str_629_ = lean_ctor_get(v_n_621_, 1);
lean_inc_ref_n(v_str_629_, 2);
lean_dec_ref_known(v_n_621_, 2);
lean_inc_ref(v_isToken_622_);
v_r_630_ = l_Lean_Name_toStringWithSep(v_sep_619_, v_escape_620_, v_pre_624_, v_isToken_622_);
v___x_631_ = lean_string_append(v_r_630_, v_sep_619_);
v___x_632_ = 0;
v___x_633_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_620_, v_str_629_, v___x_632_);
lean_inc_ref(v___x_631_);
v_r_x27_634_ = lean_string_append(v___x_631_, v___x_633_);
lean_dec_ref(v___x_633_);
if (v_escape_620_ == 0)
{
lean_dec_ref(v___x_631_);
lean_dec_ref(v_str_629_);
lean_dec_ref(v_isToken_622_);
return v_r_x27_634_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
lean_inc_ref(v_r_x27_634_);
v___x_635_ = lean_apply_1(v_isToken_622_, v_r_x27_634_);
v___x_636_ = lean_unbox(v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v___x_631_);
lean_dec_ref(v_str_629_);
return v_r_x27_634_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_r_x27_634_);
v___x_637_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_620_, v_str_629_, v_escape_620_);
v___x_638_ = lean_string_append(v___x_631_, v___x_637_);
lean_dec_ref(v___x_637_);
return v___x_638_;
}
}
}
}
default: 
{
lean_object* v_pre_639_; 
lean_dec_ref(v_isToken_622_);
v_pre_639_ = lean_ctor_get(v_n_621_, 0);
if (lean_obj_tag(v_pre_639_) == 0)
{
lean_object* v_i_640_; lean_object* v___x_641_; 
v_i_640_ = lean_ctor_get(v_n_621_, 1);
lean_inc(v_i_640_);
lean_dec_ref_known(v_n_621_, 2);
v___x_641_ = l_Nat_reprFast(v_i_640_);
return v___x_641_;
}
else
{
lean_object* v_i_642_; lean_object* v___f_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc(v_pre_639_);
v_i_642_ = lean_ctor_get(v_n_621_, 1);
lean_inc(v_i_642_);
lean_dec_ref_known(v_n_621_, 2);
v___f_643_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_644_ = l_Lean_Name_toStringWithSep(v_sep_619_, v_escape_620_, v_pre_639_, v___f_643_);
v___x_645_ = lean_string_append(v___x_644_, v_sep_619_);
v___x_646_ = l_Nat_reprFast(v_i_642_);
v___x_647_ = lean_string_append(v___x_645_, v___x_646_);
lean_dec_ref(v___x_646_);
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_648_, lean_object* v_escape_649_, lean_object* v_n_650_, lean_object* v_isToken_651_){
_start:
{
uint8_t v_escape_boxed_652_; lean_object* v_res_653_; 
v_escape_boxed_652_ = lean_unbox(v_escape_649_);
v_res_653_ = l_Lean_Name_toStringWithSep(v_sep_648_, v_escape_boxed_652_, v_n_650_, v_isToken_651_);
lean_dec_ref(v_sep_648_);
return v_res_653_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_659_ = lean_string_utf8_byte_size(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_662_ = lean_string_utf8_byte_size(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_663_){
_start:
{
lean_object* v___x_664_; uint8_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_665_ = lean_name_eq(v_n_663_, v___x_664_);
v___x_666_ = 1;
if (v___x_665_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Name_getRoot(v_n_663_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_str_668_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_str_668_ = lean_ctor_get(v___x_667_, 1);
lean_inc_ref(v_str_668_);
lean_dec_ref_known(v___x_667_, 2);
v___x_676_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_677_ = lean_string_utf8_byte_size(v_str_668_);
v___x_678_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5);
v___x_679_ = lean_nat_dec_le(v___x_678_, v___x_677_);
if (v___x_679_ == 0)
{
goto v___jp_669_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_string_memcmp(v_str_668_, v___x_676_, v___x_680_, v___x_680_, v___x_678_);
if (v___x_681_ == 0)
{
goto v___jp_669_;
}
else
{
lean_dec_ref(v_str_668_);
return v___x_666_;
}
}
v___jp_669_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_670_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_671_ = lean_string_utf8_byte_size(v_str_668_);
v___x_672_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3);
v___x_673_ = lean_nat_dec_le(v___x_672_, v___x_671_);
if (v___x_673_ == 0)
{
lean_dec_ref(v_str_668_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_string_memcmp(v_str_668_, v___x_670_, v___x_674_, v___x_674_, v___x_672_);
lean_dec_ref(v_str_668_);
return v___x_675_;
}
}
}
else
{
lean_dec(v___x_667_);
return v___x_665_;
}
}
else
{
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_682_);
lean_dec(v_n_682_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_686_, uint8_t v_escape_687_, lean_object* v_isToken_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_687_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Name_toStringWithSep(v___x_689_, v_escape_687_, v_n_686_, v_isToken_688_);
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
lean_inc(v_n_686_);
v___x_691_ = l_Lean_Name_isInaccessibleUserName(v_n_686_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; 
v___x_692_ = l_Lean_Name_hasMacroScopes(v_n_686_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_686_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Name_toStringWithSep(v___x_689_, v_escape_687_, v_n_686_, v_isToken_688_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Name_toStringWithSep(v___x_689_, v___x_692_, v_n_686_, v_isToken_688_);
return v___x_695_;
}
}
else
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Name_toStringWithSep(v___x_689_, v___x_691_, v_n_686_, v_isToken_688_);
return v___x_696_;
}
}
else
{
uint8_t v___x_697_; lean_object* v___x_698_; 
v___x_697_ = 0;
v___x_698_ = l_Lean_Name_toStringWithSep(v___x_689_, v___x_697_, v_n_686_, v_isToken_688_);
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_699_, lean_object* v_escape_700_, lean_object* v_isToken_701_){
_start:
{
uint8_t v_escape_boxed_702_; lean_object* v_res_703_; 
v_escape_boxed_702_ = lean_unbox(v_escape_700_);
v_res_703_ = l_Lean_Name_toStringWithToken(v_n_699_, v_escape_boxed_702_, v_isToken_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_704_, uint8_t v_escape_705_, lean_object* v_n_706_){
_start:
{
switch(lean_obj_tag(v_n_706_))
{
case 0:
{
lean_object* v___x_707_; 
v___x_707_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_707_;
}
case 1:
{
lean_object* v_pre_708_; 
v_pre_708_ = lean_ctor_get(v_n_706_, 0);
if (lean_obj_tag(v_pre_708_) == 0)
{
lean_object* v_str_709_; uint8_t v___x_710_; lean_object* v___x_711_; 
v_str_709_ = lean_ctor_get(v_n_706_, 1);
lean_inc_ref(v_str_709_);
lean_dec_ref_known(v_n_706_, 2);
v___x_710_ = 0;
v___x_711_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_705_, v_str_709_, v___x_710_);
return v___x_711_;
}
else
{
lean_object* v_str_712_; lean_object* v_r_713_; lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v_r_x27_717_; 
lean_inc(v_pre_708_);
v_str_712_ = lean_ctor_get(v_n_706_, 1);
lean_inc_ref(v_str_712_);
lean_dec_ref_known(v_n_706_, 2);
v_r_713_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_704_, v_escape_705_, v_pre_708_);
v___x_714_ = lean_string_append(v_r_713_, v_sep_704_);
v___x_715_ = 0;
v___x_716_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_705_, v_str_712_, v___x_715_);
v_r_x27_717_ = lean_string_append(v___x_714_, v___x_716_);
lean_dec_ref(v___x_716_);
return v_r_x27_717_;
}
}
default: 
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_n_706_, 0);
if (lean_obj_tag(v_pre_718_) == 0)
{
lean_object* v_i_719_; lean_object* v___x_720_; 
v_i_719_ = lean_ctor_get(v_n_706_, 1);
lean_inc(v_i_719_);
lean_dec_ref_known(v_n_706_, 2);
v___x_720_ = l_Nat_reprFast(v_i_719_);
return v___x_720_;
}
else
{
lean_object* v_i_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_inc(v_pre_718_);
v_i_721_ = lean_ctor_get(v_n_706_, 1);
lean_inc(v_i_721_);
lean_dec_ref_known(v_n_706_, 2);
v___x_722_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_704_, v_escape_705_, v_pre_718_);
v___x_723_ = lean_string_append(v___x_722_, v_sep_704_);
v___x_724_ = l_Nat_reprFast(v_i_721_);
v___x_725_ = lean_string_append(v___x_723_, v___x_724_);
lean_dec_ref(v___x_724_);
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_726_, lean_object* v_escape_727_, lean_object* v_n_728_){
_start:
{
uint8_t v_escape_boxed_729_; lean_object* v_res_730_; 
v_escape_boxed_729_ = lean_unbox(v_escape_727_);
v_res_730_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_726_, v_escape_boxed_729_, v_n_728_);
lean_dec_ref(v_sep_726_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_731_, uint8_t v_escape_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_732_ == 0)
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_733_, v_escape_732_, v_n_731_);
return v___x_734_;
}
else
{
uint8_t v___x_735_; 
lean_inc(v_n_731_);
v___x_735_ = l_Lean_Name_isInaccessibleUserName(v_n_731_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
v___x_736_ = l_Lean_Name_hasMacroScopes(v_n_731_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; 
v___x_737_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_731_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_733_, v_escape_732_, v_n_731_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_733_, v___x_736_, v_n_731_);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_733_, v___x_735_, v_n_731_);
return v___x_740_;
}
}
else
{
uint8_t v___x_741_; lean_object* v___x_742_; 
v___x_741_ = 0;
v___x_742_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_733_, v___x_741_, v_n_731_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_743_, lean_object* v_escape_744_){
_start:
{
uint8_t v_escape_boxed_745_; lean_object* v_res_746_; 
v_escape_boxed_745_ = lean_unbox(v_escape_744_);
v_res_746_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_743_, v_escape_boxed_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_747_, uint8_t v_escape_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_747_, v_escape_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_750_, lean_object* v_escape_751_){
_start:
{
uint8_t v_escape_boxed_752_; lean_object* v_res_753_; 
v_escape_boxed_752_ = lean_unbox(v_escape_751_);
v_res_753_ = l_Lean_Name_toString(v_n_750_, v_escape_boxed_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_754_){
_start:
{
uint8_t v___x_755_; lean_object* v___x_756_; 
v___x_755_ = 1;
v___x_756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_754_, v___x_755_);
return v___x_756_;
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
