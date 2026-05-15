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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
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
uint8_t lean_is_inaccessible_user_name(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
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
uint8_t v___y_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_string_utf8_byte_size(v_s_21_);
v___x_30_ = lean_nat_dec_lt(v_i_22_, v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; 
lean_dec(v_i_22_);
v___x_31_ = 1;
return v___x_31_;
}
else
{
uint8_t v_c_32_; uint8_t v___y_34_; uint8_t v___y_44_; uint8_t v___y_50_; uint8_t v___x_55_; uint8_t v___x_56_; 
lean_inc(v_i_22_);
v_c_32_ = lean_string_get_byte_fast(v_s_21_, v_i_22_);
v___x_55_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_56_ = lean_uint8_dec_le(v___x_55_, v_c_32_);
if (v___x_56_ == 0)
{
v___y_50_ = v___x_56_;
goto v___jp_49_;
}
else
{
uint8_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_58_ = lean_uint8_dec_le(v_c_32_, v___x_57_);
v___y_50_ = v___x_58_;
goto v___jp_49_;
}
v___jp_33_:
{
if (v___y_34_ == 0)
{
uint8_t v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_36_ = lean_uint8_dec_eq(v_c_32_, v___x_35_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1);
v___x_38_ = lean_uint8_dec_eq(v_c_32_, v___x_37_);
if (v___x_38_ == 0)
{
uint8_t v___x_39_; uint8_t v___x_40_; 
v___x_39_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2);
v___x_40_ = lean_uint8_dec_eq(v_c_32_, v___x_39_);
if (v___x_40_ == 0)
{
uint8_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3);
v___x_42_ = lean_uint8_dec_eq(v_c_32_, v___x_41_);
v___y_28_ = v___x_42_;
goto v___jp_27_;
}
else
{
v___y_28_ = v___x_40_;
goto v___jp_27_;
}
}
else
{
v___y_28_ = v___x_38_;
goto v___jp_27_;
}
}
else
{
v___y_28_ = v___x_36_;
goto v___jp_27_;
}
}
else
{
goto v___jp_23_;
}
}
v___jp_43_:
{
if (v___y_44_ == 0)
{
uint8_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4);
v___x_46_ = lean_uint8_dec_le(v___x_45_, v_c_32_);
if (v___x_46_ == 0)
{
v___y_34_ = v___x_46_;
goto v___jp_33_;
}
else
{
uint8_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5);
v___x_48_ = lean_uint8_dec_le(v_c_32_, v___x_47_);
v___y_34_ = v___x_48_;
goto v___jp_33_;
}
}
else
{
goto v___jp_23_;
}
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
uint8_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_52_ = lean_uint8_dec_le(v___x_51_, v_c_32_);
if (v___x_52_ == 0)
{
v___y_44_ = v___x_52_;
goto v___jp_43_;
}
else
{
uint8_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_54_ = lean_uint8_dec_le(v_c_32_, v___x_53_);
v___y_44_ = v___x_54_;
goto v___jp_43_;
}
}
else
{
goto v___jp_23_;
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
v___jp_27_:
{
if (v___y_28_ == 0)
{
lean_dec(v_i_22_);
return v___y_28_;
}
else
{
goto v___jp_23_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_59_, lean_object* v_i_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_59_, v_i_60_);
lean_dec_ref(v_s_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_63_){
_start:
{
lean_object* v___x_67_; uint8_t v_c_68_; uint8_t v___y_70_; uint8_t v___y_74_; uint8_t v___x_79_; uint8_t v___x_80_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v_c_68_ = lean_string_get_byte_fast(v_s_63_, v___x_67_);
v___x_79_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_80_ = lean_uint8_dec_le(v___x_79_, v_c_68_);
if (v___x_80_ == 0)
{
v___y_74_ = v___x_80_;
goto v___jp_73_;
}
else
{
uint8_t v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_82_ = lean_uint8_dec_le(v_c_68_, v___x_81_);
v___y_74_ = v___x_82_;
goto v___jp_73_;
}
v___jp_64_:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_63_, v___x_65_);
return v___x_66_;
}
v___jp_69_:
{
if (v___y_70_ == 0)
{
uint8_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_72_ = lean_uint8_dec_eq(v_c_68_, v___x_71_);
if (v___x_72_ == 0)
{
return v___x_72_;
}
else
{
goto v___jp_64_;
}
}
else
{
goto v___jp_64_;
}
}
v___jp_73_:
{
if (v___y_74_ == 0)
{
uint8_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_76_ = lean_uint8_dec_le(v___x_75_, v_c_68_);
if (v___x_76_ == 0)
{
v___y_70_ = v___x_76_;
goto v___jp_69_;
}
else
{
uint8_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_78_ = lean_uint8_dec_le(v_c_68_, v___x_77_);
v___y_70_ = v___x_78_;
goto v___jp_69_;
}
}
else
{
goto v___jp_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_83_);
lean_dec_ref(v_s_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_86_, lean_object* v_h_87_){
_start:
{
lean_object* v___x_91_; uint8_t v_c_92_; uint8_t v___y_94_; uint8_t v___y_98_; uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v_c_92_ = lean_string_get_byte_fast(v_s_86_, v___x_91_);
v___x_103_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_104_ = lean_uint8_dec_le(v___x_103_, v_c_92_);
if (v___x_104_ == 0)
{
v___y_98_ = v___x_104_;
goto v___jp_97_;
}
else
{
uint8_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_106_ = lean_uint8_dec_le(v_c_92_, v___x_105_);
v___y_98_ = v___x_106_;
goto v___jp_97_;
}
v___jp_88_:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_86_, v___x_89_);
return v___x_90_;
}
v___jp_93_:
{
if (v___y_94_ == 0)
{
uint8_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_96_ = lean_uint8_dec_eq(v_c_92_, v___x_95_);
if (v___x_96_ == 0)
{
return v___x_96_;
}
else
{
goto v___jp_88_;
}
}
else
{
goto v___jp_88_;
}
}
v___jp_97_:
{
if (v___y_98_ == 0)
{
uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_100_ = lean_uint8_dec_le(v___x_99_, v_c_92_);
if (v___x_100_ == 0)
{
v___y_94_ = v___x_100_;
goto v___jp_93_;
}
else
{
uint8_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_102_ = lean_uint8_dec_le(v_c_92_, v___x_101_);
v___y_94_ = v___x_102_;
goto v___jp_93_;
}
}
else
{
goto v___jp_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_107_, lean_object* v_h_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(v_s_107_, v_h_108_);
lean_dec_ref(v_s_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2));
v___x_115_ = lean_unsigned_to_nat(14u);
v___x_116_ = lean_unsigned_to_nat(22u);
v___x_117_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1));
v___x_118_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_121_){
_start:
{
lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v_startInclusive_126_; lean_object* v_endExclusive_127_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; uint8_t v___y_153_; uint32_t v___y_155_; uint8_t v___y_156_; uint32_t v___y_161_; uint32_t v___y_167_; uint8_t v___y_173_; lean_object* v___x_184_; uint8_t v_c_185_; uint8_t v___y_187_; uint8_t v___y_191_; uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v_c_185_ = lean_string_get_byte_fast(v_s_121_, v___x_184_);
v___x_196_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_197_ = lean_uint8_dec_le(v___x_196_, v_c_185_);
if (v___x_197_ == 0)
{
v___y_191_ = v___x_197_;
goto v___jp_190_;
}
else
{
uint8_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_199_ = lean_uint8_dec_le(v_c_185_, v___x_198_);
v___y_191_ = v___x_199_;
goto v___jp_190_;
}
v___jp_122_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
lean_inc_ref(v___y_124_);
v___x_128_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_124_);
v___x_129_ = l_String_Slice_Pos_skipWhile___redArg(v___y_125_, v___y_123_, v___x_128_);
lean_dec_ref(v___y_125_);
v___x_130_ = lean_nat_sub(v_endExclusive_127_, v_startInclusive_126_);
lean_dec(v_startInclusive_126_);
lean_dec(v_endExclusive_127_);
v___x_131_ = lean_nat_dec_eq(v___x_129_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v___x_129_);
return v___x_131_;
}
v___jp_132_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_startInclusive_138_; lean_object* v_endExclusive_139_; 
v___x_136_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_137_ = l_panic___redArg(v___y_134_, v___x_136_);
v_startInclusive_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_startInclusive_138_);
v_endExclusive_139_ = lean_ctor_get(v___x_137_, 2);
lean_inc(v_endExclusive_139_);
v___y_123_ = v___y_133_;
v___y_124_ = v___y_135_;
v___y_125_ = v___x_137_;
v_startInclusive_126_ = v_startInclusive_138_;
v_endExclusive_127_ = v_endExclusive_139_;
goto v___jp_122_;
}
v___jp_140_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_143_, 0, v_s_121_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Substring_Raw_nextn(v___x_143_, v___x_144_, v___x_141_);
lean_dec_ref(v___x_143_);
v___x_146_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_147_ = l_String_instInhabitedSlice;
v___x_148_ = lean_string_is_valid_pos(v_s_121_, v___x_145_);
if (v___x_148_ == 0)
{
lean_dec(v___x_145_);
lean_dec_ref(v_s_121_);
v___y_133_ = v___x_141_;
v___y_134_ = v___x_147_;
v___y_135_ = v___x_146_;
goto v___jp_132_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_string_is_valid_pos(v_s_121_, v___x_142_);
if (v___x_149_ == 0)
{
lean_dec(v___x_145_);
lean_dec_ref(v_s_121_);
v___y_133_ = v___x_141_;
v___y_134_ = v___x_147_;
v___y_135_ = v___x_146_;
goto v___jp_132_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v___x_145_, v___x_142_);
if (v___x_150_ == 0)
{
lean_dec(v___x_145_);
lean_dec_ref(v_s_121_);
v___y_133_ = v___x_141_;
v___y_134_ = v___x_147_;
v___y_135_ = v___x_146_;
goto v___jp_132_;
}
else
{
lean_object* v___x_151_; 
lean_inc(v___x_145_);
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_s_121_);
lean_ctor_set(v___x_151_, 1, v___x_145_);
lean_ctor_set(v___x_151_, 2, v___x_142_);
v___y_123_ = v___x_141_;
v___y_124_ = v___x_146_;
v___y_125_ = v___x_151_;
v_startInclusive_126_ = v___x_145_;
v_endExclusive_127_ = v___x_142_;
goto v___jp_122_;
}
}
}
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
lean_dec_ref(v_s_121_);
return v___y_153_;
}
else
{
goto v___jp_140_;
}
}
v___jp_154_:
{
if (v___y_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 95;
v___x_158_ = lean_uint32_dec_eq(v___y_155_, v___x_157_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; 
v___x_159_ = l_Lean_isLetterLike(v___y_155_);
v___y_153_ = v___x_159_;
goto v___jp_152_;
}
else
{
v___y_153_ = v___x_158_;
goto v___jp_152_;
}
}
else
{
goto v___jp_140_;
}
}
v___jp_160_:
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 97;
v___x_163_ = lean_uint32_dec_le(v___x_162_, v___y_161_);
if (v___x_163_ == 0)
{
v___y_155_ = v___y_161_;
v___y_156_ = v___x_163_;
goto v___jp_154_;
}
else
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 122;
v___x_165_ = lean_uint32_dec_le(v___y_161_, v___x_164_);
v___y_155_ = v___y_161_;
v___y_156_ = v___x_165_;
goto v___jp_154_;
}
}
v___jp_166_:
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 65;
v___x_169_ = lean_uint32_dec_le(v___x_168_, v___y_167_);
if (v___x_169_ == 0)
{
v___y_161_ = v___y_167_;
goto v___jp_160_;
}
else
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 90;
v___x_171_ = lean_uint32_dec_le(v___y_167_, v___x_170_);
if (v___x_171_ == 0)
{
v___y_161_ = v___y_167_;
goto v___jp_160_;
}
else
{
goto v___jp_140_;
}
}
}
v___jp_172_:
{
if (v___y_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v_s_121_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_175_);
v___x_177_ = l_String_Slice_Pos_get_x3f(v___x_176_, v___x_174_);
lean_dec_ref(v___x_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
uint32_t v___x_178_; 
v___x_178_ = 65;
v___y_167_ = v___x_178_;
goto v___jp_166_;
}
else
{
lean_object* v_val_179_; uint32_t v___x_180_; 
v_val_179_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_val_179_);
lean_dec_ref(v___x_177_);
v___x_180_ = lean_unbox_uint32(v_val_179_);
lean_dec(v_val_179_);
v___y_167_ = v___x_180_;
goto v___jp_166_;
}
}
else
{
lean_dec_ref(v_s_121_);
return v___y_173_;
}
}
v___jp_181_:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_121_, v___x_182_);
v___y_173_ = v___x_183_;
goto v___jp_172_;
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_189_ = lean_uint8_dec_eq(v_c_185_, v___x_188_);
if (v___x_189_ == 0)
{
v___y_173_ = v___x_189_;
goto v___jp_172_;
}
else
{
goto v___jp_181_;
}
}
else
{
goto v___jp_181_;
}
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_193_ = lean_uint8_dec_le(v___x_192_, v_c_185_);
if (v___x_193_ == 0)
{
v___y_187_ = v___x_193_;
goto v___jp_186_;
}
else
{
uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_195_ = lean_uint8_dec_le(v_c_185_, v___x_194_);
v___y_187_ = v___x_195_;
goto v___jp_186_;
}
}
else
{
goto v___jp_181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_203_, lean_object* v_h_204_){
_start:
{
lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v_startInclusive_209_; lean_object* v_endExclusive_210_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; uint8_t v___y_236_; uint32_t v___y_238_; uint8_t v___y_239_; uint32_t v___y_244_; uint32_t v___y_250_; uint8_t v___y_256_; lean_object* v___x_267_; uint8_t v_c_268_; uint8_t v___y_270_; uint8_t v___y_274_; uint8_t v___x_279_; uint8_t v___x_280_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v_c_268_ = lean_string_get_byte_fast(v_s_203_, v___x_267_);
v___x_279_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_280_ = lean_uint8_dec_le(v___x_279_, v_c_268_);
if (v___x_280_ == 0)
{
v___y_274_ = v___x_280_;
goto v___jp_273_;
}
else
{
uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_282_ = lean_uint8_dec_le(v_c_268_, v___x_281_);
v___y_274_ = v___x_282_;
goto v___jp_273_;
}
v___jp_205_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
lean_inc_ref(v___y_207_);
v___x_211_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_207_);
v___x_212_ = l_String_Slice_Pos_skipWhile___redArg(v___y_208_, v___y_206_, v___x_211_);
lean_dec_ref(v___y_208_);
v___x_213_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
lean_dec(v_startInclusive_209_);
lean_dec(v_endExclusive_210_);
v___x_214_ = lean_nat_dec_eq(v___x_212_, v___x_213_);
lean_dec(v___x_213_);
lean_dec(v___x_212_);
return v___x_214_;
}
v___jp_215_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_startInclusive_221_; lean_object* v_endExclusive_222_; 
v___x_219_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_220_ = l_panic___redArg(v___y_217_, v___x_219_);
v_startInclusive_221_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_startInclusive_221_);
v_endExclusive_222_ = lean_ctor_get(v___x_220_, 2);
lean_inc(v_endExclusive_222_);
v___y_206_ = v___y_216_;
v___y_207_ = v___y_218_;
v___y_208_ = v___x_220_;
v_startInclusive_209_ = v_startInclusive_221_;
v_endExclusive_210_ = v_endExclusive_222_;
goto v___jp_205_;
}
v___jp_223_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_string_utf8_byte_size(v_s_203_);
lean_inc_ref(v_s_203_);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v_s_203_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = l_Substring_Raw_nextn(v___x_226_, v___x_227_, v___x_224_);
lean_dec_ref(v___x_226_);
v___x_229_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_230_ = l_String_instInhabitedSlice;
v___x_231_ = lean_string_is_valid_pos(v_s_203_, v___x_228_);
if (v___x_231_ == 0)
{
lean_dec(v___x_228_);
lean_dec_ref(v_s_203_);
v___y_216_ = v___x_224_;
v___y_217_ = v___x_230_;
v___y_218_ = v___x_229_;
goto v___jp_215_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = lean_string_is_valid_pos(v_s_203_, v___x_225_);
if (v___x_232_ == 0)
{
lean_dec(v___x_228_);
lean_dec_ref(v_s_203_);
v___y_216_ = v___x_224_;
v___y_217_ = v___x_230_;
v___y_218_ = v___x_229_;
goto v___jp_215_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = lean_nat_dec_le(v___x_228_, v___x_225_);
if (v___x_233_ == 0)
{
lean_dec(v___x_228_);
lean_dec_ref(v_s_203_);
v___y_216_ = v___x_224_;
v___y_217_ = v___x_230_;
v___y_218_ = v___x_229_;
goto v___jp_215_;
}
else
{
lean_object* v___x_234_; 
lean_inc(v___x_228_);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v_s_203_);
lean_ctor_set(v___x_234_, 1, v___x_228_);
lean_ctor_set(v___x_234_, 2, v___x_225_);
v___y_206_ = v___x_224_;
v___y_207_ = v___x_229_;
v___y_208_ = v___x_234_;
v_startInclusive_209_ = v___x_228_;
v_endExclusive_210_ = v___x_225_;
goto v___jp_205_;
}
}
}
}
v___jp_235_:
{
if (v___y_236_ == 0)
{
lean_dec_ref(v_s_203_);
return v___y_236_;
}
else
{
goto v___jp_223_;
}
}
v___jp_237_:
{
if (v___y_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 95;
v___x_241_ = lean_uint32_dec_eq(v___y_238_, v___x_240_);
if (v___x_241_ == 0)
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_isLetterLike(v___y_238_);
v___y_236_ = v___x_242_;
goto v___jp_235_;
}
else
{
v___y_236_ = v___x_241_;
goto v___jp_235_;
}
}
else
{
goto v___jp_223_;
}
}
v___jp_243_:
{
uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 97;
v___x_246_ = lean_uint32_dec_le(v___x_245_, v___y_244_);
if (v___x_246_ == 0)
{
v___y_238_ = v___y_244_;
v___y_239_ = v___x_246_;
goto v___jp_237_;
}
else
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 122;
v___x_248_ = lean_uint32_dec_le(v___y_244_, v___x_247_);
v___y_238_ = v___y_244_;
v___y_239_ = v___x_248_;
goto v___jp_237_;
}
}
v___jp_249_:
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 65;
v___x_252_ = lean_uint32_dec_le(v___x_251_, v___y_250_);
if (v___x_252_ == 0)
{
v___y_244_ = v___y_250_;
goto v___jp_243_;
}
else
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 90;
v___x_254_ = lean_uint32_dec_le(v___y_250_, v___x_253_);
if (v___x_254_ == 0)
{
v___y_244_ = v___y_250_;
goto v___jp_243_;
}
else
{
goto v___jp_223_;
}
}
}
v___jp_255_:
{
if (v___y_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_string_utf8_byte_size(v_s_203_);
lean_inc_ref(v_s_203_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v_s_203_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
lean_ctor_set(v___x_259_, 2, v___x_258_);
v___x_260_ = l_String_Slice_Pos_get_x3f(v___x_259_, v___x_257_);
lean_dec_ref(v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
uint32_t v___x_261_; 
v___x_261_ = 65;
v___y_250_ = v___x_261_;
goto v___jp_249_;
}
else
{
lean_object* v_val_262_; uint32_t v___x_263_; 
v_val_262_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v___x_260_);
v___x_263_ = lean_unbox_uint32(v_val_262_);
lean_dec(v_val_262_);
v___y_250_ = v___x_263_;
goto v___jp_249_;
}
}
else
{
lean_dec_ref(v_s_203_);
return v___y_256_;
}
}
v___jp_264_:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_203_, v___x_265_);
v___y_256_ = v___x_266_;
goto v___jp_255_;
}
v___jp_269_:
{
if (v___y_270_ == 0)
{
uint8_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_272_ = lean_uint8_dec_eq(v_c_268_, v___x_271_);
if (v___x_272_ == 0)
{
v___y_256_ = v___x_272_;
goto v___jp_255_;
}
else
{
goto v___jp_264_;
}
}
else
{
goto v___jp_264_;
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_276_ = lean_uint8_dec_le(v___x_275_, v_c_268_);
if (v___x_276_ == 0)
{
v___y_270_ = v___x_276_;
goto v___jp_269_;
}
else
{
uint8_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_278_ = lean_uint8_dec_le(v_c_268_, v___x_277_);
v___y_270_ = v___x_278_;
goto v___jp_269_;
}
}
else
{
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_283_, lean_object* v_h_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_283_, v_h_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = l_Lean_idBeginEscape;
v___x_289_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_290_ = lean_string_push(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = l_Lean_idEndEscape;
v___x_292_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_293_ = lean_string_push(v___x_292_, v___x_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_295_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_296_ = lean_string_append(v___x_295_, v_s_294_);
v___x_297_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_299_);
lean_dec_ref(v_s_299_);
return v_res_300_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_303_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_312_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_304_, v___x_311_, v___y_305_, lean_box(0), lean_box(0), v___y_308_, v___y_309_, v___y_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_316_, uint8_t v_force_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_string_utf8_byte_size(v_s_316_);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_322_ = lean_string_append(v___x_321_, v_s_316_);
lean_dec_ref(v_s_316_);
v___x_323_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v___f_326_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v_startInclusive_341_; lean_object* v_endExclusive_342_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_367_; uint32_t v___y_369_; uint8_t v___y_370_; uint32_t v___y_375_; uint32_t v___y_381_; uint8_t v___y_387_; 
v___f_326_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_317_ == 0)
{
uint8_t v_c_397_; uint8_t v___y_399_; uint8_t v___y_403_; uint8_t v___x_408_; uint8_t v___x_409_; 
v_c_397_ = lean_string_get_byte_fast(v_s_316_, v___x_318_);
v___x_408_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_409_ = lean_uint8_dec_le(v___x_408_, v_c_397_);
if (v___x_409_ == 0)
{
v___y_403_ = v___x_409_;
goto v___jp_402_;
}
else
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_411_ = lean_uint8_dec_le(v_c_397_, v___x_410_);
v___y_403_ = v___x_411_;
goto v___jp_402_;
}
v___jp_398_:
{
if (v___y_399_ == 0)
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_401_ = lean_uint8_dec_eq(v_c_397_, v___x_400_);
if (v___x_401_ == 0)
{
v___y_387_ = v___x_401_;
goto v___jp_386_;
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
v___jp_402_:
{
if (v___y_403_ == 0)
{
uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_405_ = lean_uint8_dec_le(v___x_404_, v_c_397_);
if (v___x_405_ == 0)
{
v___y_399_ = v___x_405_;
goto v___jp_398_;
}
else
{
uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_407_ = lean_uint8_dec_le(v_c_397_, v___x_406_);
v___y_399_ = v___x_407_;
goto v___jp_398_;
}
}
else
{
goto v___jp_394_;
}
}
}
else
{
goto v___jp_327_;
}
v___jp_327_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_316_);
v___x_329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_329_, 0, v_s_316_);
lean_ctor_set(v___x_329_, 1, v___x_318_);
lean_ctor_set(v___x_329_, 2, v___x_319_);
v___x_330_ = l_String_Slice_contains___redArg(v___f_326_, v___x_329_, v___x_328_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_332_ = lean_string_append(v___x_331_, v_s_316_);
lean_dec_ref(v_s_316_);
v___x_333_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_334_ = lean_string_append(v___x_332_, v___x_333_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
lean_dec_ref(v_s_316_);
v___x_336_ = lean_box(0);
return v___x_336_;
}
}
v___jp_337_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
lean_inc_ref(v___y_339_);
v___x_343_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_339_);
v___x_344_ = l_String_Slice_Pos_skipWhile___redArg(v___y_340_, v___y_338_, v___x_343_);
lean_dec_ref(v___y_340_);
v___x_345_ = lean_nat_sub(v_endExclusive_342_, v_startInclusive_341_);
lean_dec(v_startInclusive_341_);
lean_dec(v_endExclusive_342_);
v___x_346_ = lean_nat_dec_eq(v___x_344_, v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_344_);
if (v___x_346_ == 0)
{
goto v___jp_327_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v_s_316_);
return v___x_347_;
}
}
v___jp_348_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_startInclusive_354_; lean_object* v_endExclusive_355_; 
v___x_352_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_353_ = l_panic___redArg(v___y_351_, v___x_352_);
v_startInclusive_354_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_startInclusive_354_);
v_endExclusive_355_ = lean_ctor_get(v___x_353_, 2);
lean_inc(v_endExclusive_355_);
v___y_338_ = v___y_349_;
v___y_339_ = v___y_350_;
v___y_340_ = v___x_353_;
v_startInclusive_341_ = v_startInclusive_354_;
v_endExclusive_342_ = v_endExclusive_355_;
goto v___jp_337_;
}
v___jp_356_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
lean_inc_ref(v_s_316_);
v___x_357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_357_, 0, v_s_316_);
lean_ctor_set(v___x_357_, 1, v___x_318_);
lean_ctor_set(v___x_357_, 2, v___x_319_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = l_Substring_Raw_nextn(v___x_357_, v___x_358_, v___x_318_);
lean_dec_ref(v___x_357_);
v___x_360_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_361_ = l_String_instInhabitedSlice;
v___x_362_ = lean_string_is_valid_pos(v_s_316_, v___x_359_);
if (v___x_362_ == 0)
{
lean_dec(v___x_359_);
v___y_349_ = v___x_318_;
v___y_350_ = v___x_360_;
v___y_351_ = v___x_361_;
goto v___jp_348_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = lean_string_is_valid_pos(v_s_316_, v___x_319_);
if (v___x_363_ == 0)
{
lean_dec(v___x_359_);
v___y_349_ = v___x_318_;
v___y_350_ = v___x_360_;
v___y_351_ = v___x_361_;
goto v___jp_348_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = lean_nat_dec_le(v___x_359_, v___x_319_);
if (v___x_364_ == 0)
{
lean_dec(v___x_359_);
v___y_349_ = v___x_318_;
v___y_350_ = v___x_360_;
v___y_351_ = v___x_361_;
goto v___jp_348_;
}
else
{
lean_object* v___x_365_; 
lean_inc(v___x_359_);
lean_inc_ref(v_s_316_);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v_s_316_);
lean_ctor_set(v___x_365_, 1, v___x_359_);
lean_ctor_set(v___x_365_, 2, v___x_319_);
v___y_338_ = v___x_318_;
v___y_339_ = v___x_360_;
v___y_340_ = v___x_365_;
v_startInclusive_341_ = v___x_359_;
v_endExclusive_342_ = v___x_319_;
goto v___jp_337_;
}
}
}
}
v___jp_366_:
{
if (v___y_367_ == 0)
{
goto v___jp_327_;
}
else
{
goto v___jp_356_;
}
}
v___jp_368_:
{
if (v___y_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 95;
v___x_372_ = lean_uint32_dec_eq(v___y_369_, v___x_371_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; 
v___x_373_ = l_Lean_isLetterLike(v___y_369_);
v___y_367_ = v___x_373_;
goto v___jp_366_;
}
else
{
v___y_367_ = v___x_372_;
goto v___jp_366_;
}
}
else
{
goto v___jp_356_;
}
}
v___jp_374_:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 97;
v___x_377_ = lean_uint32_dec_le(v___x_376_, v___y_375_);
if (v___x_377_ == 0)
{
v___y_369_ = v___y_375_;
v___y_370_ = v___x_377_;
goto v___jp_368_;
}
else
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 122;
v___x_379_ = lean_uint32_dec_le(v___y_375_, v___x_378_);
v___y_369_ = v___y_375_;
v___y_370_ = v___x_379_;
goto v___jp_368_;
}
}
v___jp_380_:
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 65;
v___x_383_ = lean_uint32_dec_le(v___x_382_, v___y_381_);
if (v___x_383_ == 0)
{
v___y_375_ = v___y_381_;
goto v___jp_374_;
}
else
{
uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 90;
v___x_385_ = lean_uint32_dec_le(v___y_381_, v___x_384_);
if (v___x_385_ == 0)
{
v___y_375_ = v___y_381_;
goto v___jp_374_;
}
else
{
goto v___jp_356_;
}
}
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_inc_ref(v_s_316_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v_s_316_);
lean_ctor_set(v___x_388_, 1, v___x_318_);
lean_ctor_set(v___x_388_, 2, v___x_319_);
v___x_389_ = l_String_Slice_Pos_get_x3f(v___x_388_, v___x_318_);
lean_dec_ref(v___x_388_);
if (lean_obj_tag(v___x_389_) == 0)
{
uint32_t v___x_390_; 
v___x_390_ = 65;
v___y_381_ = v___x_390_;
goto v___jp_380_;
}
else
{
lean_object* v_val_391_; uint32_t v___x_392_; 
v_val_391_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_391_);
lean_dec_ref(v___x_389_);
v___x_392_ = lean_unbox_uint32(v_val_391_);
lean_dec(v_val_391_);
v___y_381_ = v___x_392_;
goto v___jp_380_;
}
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_s_316_);
return v___x_393_;
}
}
v___jp_394_:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_316_, v___x_395_);
v___y_387_ = v___x_396_;
goto v___jp_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_412_, lean_object* v_force_413_){
_start:
{
uint8_t v_force_boxed_414_; lean_object* v_res_415_; 
v_force_boxed_414_ = lean_unbox(v_force_413_);
v_res_415_ = l_Lean_Name_escapePart(v_s_412_, v_force_boxed_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = l_String_instInhabitedSlice;
v___x_418_ = lean_panic_fn_borrowed(v___x_417_, v_msg_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_419_, lean_object* v_pos_420_){
_start:
{
lean_object* v_str_421_; lean_object* v_startInclusive_422_; lean_object* v_endExclusive_423_; lean_object* v___x_424_; uint8_t v___y_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_str_421_ = lean_ctor_get(v_s_419_, 0);
v_startInclusive_422_ = lean_ctor_get(v_s_419_, 1);
v_endExclusive_423_ = lean_ctor_get(v_s_419_, 2);
v___x_424_ = lean_nat_add(v_startInclusive_422_, v_pos_420_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_nat_sub(v_endExclusive_423_, v___x_424_);
v___x_435_ = lean_nat_dec_eq(v___x_433_, v___x_434_);
lean_dec(v___x_434_);
if (v___x_435_ == 0)
{
uint32_t v___x_436_; uint8_t v___y_438_; uint8_t v___y_450_; uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_436_ = lean_string_utf8_get_fast(v_str_421_, v___x_424_);
v___x_460_ = 65;
v___x_461_ = lean_uint32_dec_le(v___x_460_, v___x_436_);
if (v___x_461_ == 0)
{
goto v___jp_455_;
}
else
{
uint32_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 90;
v___x_463_ = lean_uint32_dec_le(v___x_436_, v___x_462_);
if (v___x_463_ == 0)
{
goto v___jp_455_;
}
else
{
goto v___jp_425_;
}
}
v___jp_437_:
{
if (v___y_438_ == 0)
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 95;
v___x_440_ = lean_uint32_dec_eq(v___x_436_, v___x_439_);
if (v___x_440_ == 0)
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 39;
v___x_442_ = lean_uint32_dec_eq(v___x_436_, v___x_441_);
if (v___x_442_ == 0)
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 33;
v___x_444_ = lean_uint32_dec_eq(v___x_436_, v___x_443_);
if (v___x_444_ == 0)
{
uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 63;
v___x_446_ = lean_uint32_dec_eq(v___x_436_, v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_isLetterLike(v___x_436_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_isSubScriptAlnum(v___x_436_);
v___y_432_ = v___x_448_;
goto v___jp_431_;
}
else
{
v___y_432_ = v___x_447_;
goto v___jp_431_;
}
}
else
{
v___y_432_ = v___x_446_;
goto v___jp_431_;
}
}
else
{
v___y_432_ = v___x_444_;
goto v___jp_431_;
}
}
else
{
v___y_432_ = v___x_442_;
goto v___jp_431_;
}
}
else
{
v___y_432_ = v___x_440_;
goto v___jp_431_;
}
}
else
{
goto v___jp_425_;
}
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 48;
v___x_452_ = lean_uint32_dec_le(v___x_451_, v___x_436_);
if (v___x_452_ == 0)
{
v___y_438_ = v___x_452_;
goto v___jp_437_;
}
else
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 57;
v___x_454_ = lean_uint32_dec_le(v___x_436_, v___x_453_);
v___y_438_ = v___x_454_;
goto v___jp_437_;
}
}
else
{
goto v___jp_425_;
}
}
v___jp_455_:
{
uint32_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 97;
v___x_457_ = lean_uint32_dec_le(v___x_456_, v___x_436_);
if (v___x_457_ == 0)
{
v___y_450_ = v___x_457_;
goto v___jp_449_;
}
else
{
uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 122;
v___x_459_ = lean_uint32_dec_le(v___x_436_, v___x_458_);
v___y_450_ = v___x_459_;
goto v___jp_449_;
}
}
}
else
{
lean_dec(v___x_424_);
return v_pos_420_;
}
v___jp_425_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_426_ = lean_string_utf8_next_fast(v_str_421_, v___x_424_);
v___x_427_ = lean_nat_sub(v___x_426_, v___x_424_);
lean_dec(v___x_424_);
v___x_428_ = lean_nat_add(v_pos_420_, v___x_427_);
lean_dec(v___x_427_);
v___x_429_ = lean_nat_dec_lt(v_pos_420_, v___x_428_);
if (v___x_429_ == 0)
{
lean_dec(v___x_428_);
return v_pos_420_;
}
else
{
lean_dec(v_pos_420_);
v_pos_420_ = v___x_428_;
goto _start;
}
}
v___jp_431_:
{
if (v___y_432_ == 0)
{
lean_dec(v___x_424_);
return v_pos_420_;
}
else
{
goto v___jp_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_464_, lean_object* v_pos_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_464_, v_pos_465_);
lean_dec_ref(v_s_464_);
return v_res_466_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_467_, lean_object* v_a_468_, uint8_t v_b_469_){
_start:
{
lean_object* v_str_470_; lean_object* v_startInclusive_471_; lean_object* v_endExclusive_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_str_470_ = lean_ctor_get(v_s_467_, 0);
v_startInclusive_471_ = lean_ctor_get(v_s_467_, 1);
v_endExclusive_472_ = lean_ctor_get(v_s_467_, 2);
v___x_473_ = lean_nat_sub(v_endExclusive_472_, v_startInclusive_471_);
v___x_474_ = lean_nat_dec_eq(v_a_468_, v___x_473_);
lean_dec(v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_nat_add(v_startInclusive_471_, v_a_468_);
lean_dec(v_a_468_);
v___x_476_ = lean_string_utf8_get_fast(v_str_470_, v___x_475_);
v___x_477_ = 187;
v___x_478_ = lean_uint32_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_string_utf8_next_fast(v_str_470_, v___x_475_);
lean_dec(v___x_475_);
v___x_480_ = lean_nat_sub(v___x_479_, v_startInclusive_471_);
v_a_468_ = v___x_480_;
v_b_469_ = v___x_478_;
goto _start;
}
else
{
lean_dec(v___x_475_);
return v___x_478_;
}
}
else
{
lean_dec(v_a_468_);
return v_b_469_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_482_, lean_object* v_a_483_, lean_object* v_b_484_){
_start:
{
uint8_t v_b_boxed_485_; uint8_t v_res_486_; lean_object* v_r_487_; 
v_b_boxed_485_ = lean_unbox(v_b_484_);
v_res_486_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_482_, v_a_483_, v_b_boxed_485_);
lean_dec_ref(v_s_482_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_488_){
_start:
{
lean_object* v_searcher_489_; uint8_t v___x_490_; uint8_t v___x_491_; 
v_searcher_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = 0;
v___x_491_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_488_, v_searcher_489_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_492_);
lean_dec_ref(v_s_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_495_, lean_object* v_s_496_, uint8_t v_force_497_){
_start:
{
lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v_startInclusive_510_; lean_object* v_endExclusive_511_; lean_object* v___y_516_; uint8_t v___y_532_; uint32_t v___y_534_; uint8_t v___y_535_; uint32_t v___y_540_; uint32_t v___y_546_; uint8_t v___y_552_; 
if (v_escape_495_ == 0)
{
return v_s_496_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_string_utf8_byte_size(v_s_496_);
v___x_565_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_567_ = lean_string_append(v___x_566_, v_s_496_);
lean_dec_ref(v_s_496_);
v___x_568_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
return v___x_569_;
}
else
{
if (v_force_497_ == 0)
{
uint8_t v_c_570_; uint8_t v___y_572_; uint8_t v___y_576_; uint8_t v___x_581_; uint8_t v___x_582_; 
v_c_570_ = lean_string_get_byte_fast(v_s_496_, v___x_563_);
v___x_581_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_582_ = lean_uint8_dec_le(v___x_581_, v_c_570_);
if (v___x_582_ == 0)
{
v___y_576_ = v___x_582_;
goto v___jp_575_;
}
else
{
uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_584_ = lean_uint8_dec_le(v_c_570_, v___x_583_);
v___y_576_ = v___x_584_;
goto v___jp_575_;
}
v___jp_571_:
{
if (v___y_572_ == 0)
{
uint8_t v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_574_ = lean_uint8_dec_eq(v_c_570_, v___x_573_);
if (v___x_574_ == 0)
{
v___y_552_ = v___x_574_;
goto v___jp_551_;
}
else
{
goto v___jp_560_;
}
}
else
{
goto v___jp_560_;
}
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
uint8_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_578_ = lean_uint8_dec_le(v___x_577_, v_c_570_);
if (v___x_578_ == 0)
{
v___y_572_ = v___x_578_;
goto v___jp_571_;
}
else
{
uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_580_ = lean_uint8_dec_le(v_c_570_, v___x_579_);
v___y_572_ = v___x_580_;
goto v___jp_571_;
}
}
else
{
goto v___jp_560_;
}
}
}
else
{
goto v___jp_498_;
}
}
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_string_utf8_byte_size(v_s_496_);
lean_inc_ref(v_s_496_);
v___x_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_501_, 0, v_s_496_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
lean_ctor_set(v___x_501_, 2, v___x_500_);
v___x_502_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_501_);
lean_dec_ref(v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_504_ = lean_string_append(v___x_503_, v_s_496_);
lean_dec_ref(v_s_496_);
v___x_505_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_506_ = lean_string_append(v___x_504_, v___x_505_);
return v___x_506_;
}
else
{
return v_s_496_;
}
}
v___jp_507_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_509_, v___y_508_);
lean_dec_ref(v___y_509_);
v___x_513_ = lean_nat_sub(v_endExclusive_511_, v_startInclusive_510_);
lean_dec(v_startInclusive_510_);
lean_dec(v_endExclusive_511_);
v___x_514_ = lean_nat_dec_eq(v___x_512_, v___x_513_);
lean_dec(v___x_513_);
lean_dec(v___x_512_);
if (v___x_514_ == 0)
{
goto v___jp_498_;
}
else
{
return v_s_496_;
}
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_startInclusive_519_; lean_object* v_endExclusive_520_; 
v___x_517_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_518_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_517_);
v_startInclusive_519_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_startInclusive_519_);
v_endExclusive_520_ = lean_ctor_get(v___x_518_, 2);
lean_inc(v_endExclusive_520_);
v___y_508_ = v___y_516_;
v___y_509_ = v___x_518_;
v_startInclusive_510_ = v_startInclusive_519_;
v_endExclusive_511_ = v_endExclusive_520_;
goto v___jp_507_;
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_string_utf8_byte_size(v_s_496_);
lean_inc_ref(v_s_496_);
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v_s_496_);
lean_ctor_set(v___x_524_, 1, v___x_522_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = l_Substring_Raw_nextn(v___x_524_, v___x_525_, v___x_522_);
lean_dec_ref(v___x_524_);
v___x_527_ = lean_string_is_valid_pos(v_s_496_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec(v___x_526_);
v___y_516_ = v___x_522_;
goto v___jp_515_;
}
else
{
uint8_t v___x_528_; 
v___x_528_ = lean_string_is_valid_pos(v_s_496_, v___x_523_);
if (v___x_528_ == 0)
{
lean_dec(v___x_526_);
v___y_516_ = v___x_522_;
goto v___jp_515_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_le(v___x_526_, v___x_523_);
if (v___x_529_ == 0)
{
lean_dec(v___x_526_);
v___y_516_ = v___x_522_;
goto v___jp_515_;
}
else
{
lean_object* v___x_530_; 
lean_inc(v___x_526_);
lean_inc_ref(v_s_496_);
v___x_530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_530_, 0, v_s_496_);
lean_ctor_set(v___x_530_, 1, v___x_526_);
lean_ctor_set(v___x_530_, 2, v___x_523_);
v___y_508_ = v___x_522_;
v___y_509_ = v___x_530_;
v_startInclusive_510_ = v___x_526_;
v_endExclusive_511_ = v___x_523_;
goto v___jp_507_;
}
}
}
}
v___jp_531_:
{
if (v___y_532_ == 0)
{
goto v___jp_498_;
}
else
{
goto v___jp_521_;
}
}
v___jp_533_:
{
if (v___y_535_ == 0)
{
uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 95;
v___x_537_ = lean_uint32_dec_eq(v___y_534_, v___x_536_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_isLetterLike(v___y_534_);
v___y_532_ = v___x_538_;
goto v___jp_531_;
}
else
{
v___y_532_ = v___x_537_;
goto v___jp_531_;
}
}
else
{
goto v___jp_521_;
}
}
v___jp_539_:
{
uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = 97;
v___x_542_ = lean_uint32_dec_le(v___x_541_, v___y_540_);
if (v___x_542_ == 0)
{
v___y_534_ = v___y_540_;
v___y_535_ = v___x_542_;
goto v___jp_533_;
}
else
{
uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = 122;
v___x_544_ = lean_uint32_dec_le(v___y_540_, v___x_543_);
v___y_534_ = v___y_540_;
v___y_535_ = v___x_544_;
goto v___jp_533_;
}
}
v___jp_545_:
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 65;
v___x_548_ = lean_uint32_dec_le(v___x_547_, v___y_546_);
if (v___x_548_ == 0)
{
v___y_540_ = v___y_546_;
goto v___jp_539_;
}
else
{
uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 90;
v___x_550_ = lean_uint32_dec_le(v___y_546_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_540_ = v___y_546_;
goto v___jp_539_;
}
else
{
goto v___jp_521_;
}
}
}
v___jp_551_:
{
if (v___y_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_string_utf8_byte_size(v_s_496_);
lean_inc_ref(v_s_496_);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v_s_496_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
lean_ctor_set(v___x_555_, 2, v___x_554_);
v___x_556_ = l_String_Slice_Pos_get_x3f(v___x_555_, v___x_553_);
lean_dec_ref(v___x_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
uint32_t v___x_557_; 
v___x_557_ = 65;
v___y_546_ = v___x_557_;
goto v___jp_545_;
}
else
{
lean_object* v_val_558_; uint32_t v___x_559_; 
v_val_558_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_558_);
lean_dec_ref(v___x_556_);
v___x_559_ = lean_unbox_uint32(v_val_558_);
lean_dec(v_val_558_);
v___y_546_ = v___x_559_;
goto v___jp_545_;
}
}
else
{
return v_s_496_;
}
}
v___jp_560_:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_496_, v___x_561_);
v___y_552_ = v___x_562_;
goto v___jp_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_585_, lean_object* v_s_586_, lean_object* v_force_587_){
_start:
{
uint8_t v_escape_boxed_588_; uint8_t v_force_boxed_589_; lean_object* v_res_590_; 
v_escape_boxed_588_ = lean_unbox(v_escape_585_);
v_force_boxed_589_ = lean_unbox(v_force_587_);
v_res_590_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_588_, v_s_586_, v_force_boxed_589_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_591_, lean_object* v_inst_592_, lean_object* v_R_593_, lean_object* v_a_594_, uint8_t v_b_595_, lean_object* v_c_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_591_, v_a_594_, v_b_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_598_, lean_object* v_inst_599_, lean_object* v_R_600_, lean_object* v_a_601_, lean_object* v_b_602_, lean_object* v_c_603_){
_start:
{
uint8_t v_b_boxed_604_; uint8_t v_res_605_; lean_object* v_r_606_; 
v_b_boxed_604_ = lean_unbox(v_b_602_);
v_res_605_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_598_, v_inst_599_, v_R_600_, v_a_601_, v_b_boxed_604_, v_c_603_);
lean_dec_ref(v_s_598_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = 0;
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_Name_toStringWithSep___lam__0(v_x_609_);
lean_dec_ref(v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_614_, uint8_t v_escape_615_, lean_object* v_n_616_, lean_object* v_isToken_617_){
_start:
{
switch(lean_obj_tag(v_n_616_))
{
case 0:
{
lean_object* v___x_618_; 
lean_dec_ref(v_isToken_617_);
v___x_618_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_618_;
}
case 1:
{
lean_object* v_pre_619_; 
v_pre_619_ = lean_ctor_get(v_n_616_, 0);
if (lean_obj_tag(v_pre_619_) == 0)
{
lean_object* v_str_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; 
v_str_620_ = lean_ctor_get(v_n_616_, 1);
lean_inc_ref_n(v_str_620_, 2);
lean_dec_ref(v_n_616_);
v___x_621_ = lean_apply_1(v_isToken_617_, v_str_620_);
v___x_622_ = lean_unbox(v___x_621_);
v___x_623_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_615_, v_str_620_, v___x_622_);
return v___x_623_;
}
else
{
lean_object* v_str_624_; lean_object* v_r_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v_r_x27_629_; 
lean_inc(v_pre_619_);
v_str_624_ = lean_ctor_get(v_n_616_, 1);
lean_inc_ref_n(v_str_624_, 2);
lean_dec_ref(v_n_616_);
lean_inc_ref(v_isToken_617_);
v_r_625_ = l_Lean_Name_toStringWithSep(v_sep_614_, v_escape_615_, v_pre_619_, v_isToken_617_);
v___x_626_ = lean_string_append(v_r_625_, v_sep_614_);
v___x_627_ = 0;
v___x_628_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_615_, v_str_624_, v___x_627_);
lean_inc_ref(v___x_626_);
v_r_x27_629_ = lean_string_append(v___x_626_, v___x_628_);
lean_dec_ref(v___x_628_);
if (v_escape_615_ == 0)
{
lean_dec_ref(v___x_626_);
lean_dec_ref(v_str_624_);
lean_dec_ref(v_isToken_617_);
return v_r_x27_629_;
}
else
{
lean_object* v___x_630_; uint8_t v___x_631_; 
lean_inc_ref(v_r_x27_629_);
v___x_630_ = lean_apply_1(v_isToken_617_, v_r_x27_629_);
v___x_631_ = lean_unbox(v___x_630_);
if (v___x_631_ == 0)
{
lean_dec_ref(v___x_626_);
lean_dec_ref(v_str_624_);
return v_r_x27_629_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_r_x27_629_);
v___x_632_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_615_, v_str_624_, v_escape_615_);
v___x_633_ = lean_string_append(v___x_626_, v___x_632_);
lean_dec_ref(v___x_632_);
return v___x_633_;
}
}
}
}
default: 
{
lean_object* v_pre_634_; 
lean_dec_ref(v_isToken_617_);
v_pre_634_ = lean_ctor_get(v_n_616_, 0);
if (lean_obj_tag(v_pre_634_) == 0)
{
lean_object* v_i_635_; lean_object* v___x_636_; 
v_i_635_ = lean_ctor_get(v_n_616_, 1);
lean_inc(v_i_635_);
lean_dec_ref(v_n_616_);
v___x_636_ = l_Nat_reprFast(v_i_635_);
return v___x_636_;
}
else
{
lean_object* v_i_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_inc(v_pre_634_);
v_i_637_ = lean_ctor_get(v_n_616_, 1);
lean_inc(v_i_637_);
lean_dec_ref(v_n_616_);
v___f_638_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_639_ = l_Lean_Name_toStringWithSep(v_sep_614_, v_escape_615_, v_pre_634_, v___f_638_);
v___x_640_ = lean_string_append(v___x_639_, v_sep_614_);
v___x_641_ = l_Nat_reprFast(v_i_637_);
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
lean_dec_ref(v___x_641_);
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_643_, lean_object* v_escape_644_, lean_object* v_n_645_, lean_object* v_isToken_646_){
_start:
{
uint8_t v_escape_boxed_647_; lean_object* v_res_648_; 
v_escape_boxed_647_ = lean_unbox(v_escape_644_);
v_res_648_ = l_Lean_Name_toStringWithSep(v_sep_643_, v_escape_boxed_647_, v_n_645_, v_isToken_646_);
lean_dec_ref(v_sep_643_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_654_ = lean_string_utf8_byte_size(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_657_ = lean_string_utf8_byte_size(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_658_){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; uint8_t v___x_661_; 
v___x_659_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_660_ = lean_name_eq(v_n_658_, v___x_659_);
v___x_661_ = 1;
if (v___x_660_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Name_getRoot(v_n_658_);
if (lean_obj_tag(v___x_662_) == 1)
{
lean_object* v_str_663_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_str_663_ = lean_ctor_get(v___x_662_, 1);
lean_inc_ref(v_str_663_);
lean_dec_ref(v___x_662_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_672_ = lean_string_utf8_byte_size(v_str_663_);
v___x_673_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5);
v___x_674_ = lean_nat_dec_le(v___x_673_, v___x_672_);
if (v___x_674_ == 0)
{
goto v___jp_664_;
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_string_memcmp(v_str_663_, v___x_671_, v___x_675_, v___x_675_, v___x_673_);
if (v___x_676_ == 0)
{
goto v___jp_664_;
}
else
{
lean_dec_ref(v_str_663_);
return v___x_661_;
}
}
v___jp_664_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_665_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_666_ = lean_string_utf8_byte_size(v_str_663_);
v___x_667_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3);
v___x_668_ = lean_nat_dec_le(v___x_667_, v___x_666_);
if (v___x_668_ == 0)
{
lean_dec_ref(v_str_663_);
return v___x_660_;
}
else
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_string_memcmp(v_str_663_, v___x_665_, v___x_669_, v___x_669_, v___x_667_);
lean_dec_ref(v_str_663_);
return v___x_670_;
}
}
}
else
{
lean_dec(v___x_662_);
return v___x_660_;
}
}
else
{
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_677_);
lean_dec(v_n_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_681_, uint8_t v_escape_682_, lean_object* v_isToken_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_682_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Name_toStringWithSep(v___x_684_, v_escape_682_, v_n_681_, v_isToken_683_);
return v___x_685_;
}
else
{
uint8_t v___x_686_; 
lean_inc(v_n_681_);
v___x_686_ = lean_is_inaccessible_user_name(v_n_681_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_Name_hasMacroScopes(v_n_681_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; 
v___x_688_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_681_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Name_toStringWithSep(v___x_684_, v_escape_682_, v_n_681_, v_isToken_683_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Name_toStringWithSep(v___x_684_, v___x_687_, v_n_681_, v_isToken_683_);
return v___x_690_;
}
}
else
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Name_toStringWithSep(v___x_684_, v___x_686_, v_n_681_, v_isToken_683_);
return v___x_691_;
}
}
else
{
uint8_t v___x_692_; lean_object* v___x_693_; 
v___x_692_ = 0;
v___x_693_ = l_Lean_Name_toStringWithSep(v___x_684_, v___x_692_, v_n_681_, v_isToken_683_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_694_, lean_object* v_escape_695_, lean_object* v_isToken_696_){
_start:
{
uint8_t v_escape_boxed_697_; lean_object* v_res_698_; 
v_escape_boxed_697_ = lean_unbox(v_escape_695_);
v_res_698_ = l_Lean_Name_toStringWithToken(v_n_694_, v_escape_boxed_697_, v_isToken_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_699_, uint8_t v_escape_700_, lean_object* v_n_701_){
_start:
{
switch(lean_obj_tag(v_n_701_))
{
case 0:
{
lean_object* v___x_702_; 
v___x_702_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_702_;
}
case 1:
{
lean_object* v_pre_703_; 
v_pre_703_ = lean_ctor_get(v_n_701_, 0);
if (lean_obj_tag(v_pre_703_) == 0)
{
lean_object* v_str_704_; uint8_t v___x_705_; lean_object* v___x_706_; 
v_str_704_ = lean_ctor_get(v_n_701_, 1);
lean_inc_ref(v_str_704_);
lean_dec_ref(v_n_701_);
v___x_705_ = 0;
v___x_706_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_700_, v_str_704_, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v_str_707_; lean_object* v_r_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v_r_x27_712_; 
lean_inc(v_pre_703_);
v_str_707_ = lean_ctor_get(v_n_701_, 1);
lean_inc_ref(v_str_707_);
lean_dec_ref(v_n_701_);
v_r_708_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_699_, v_escape_700_, v_pre_703_);
v___x_709_ = lean_string_append(v_r_708_, v_sep_699_);
v___x_710_ = 0;
v___x_711_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_700_, v_str_707_, v___x_710_);
v_r_x27_712_ = lean_string_append(v___x_709_, v___x_711_);
lean_dec_ref(v___x_711_);
return v_r_x27_712_;
}
}
default: 
{
lean_object* v_pre_713_; 
v_pre_713_ = lean_ctor_get(v_n_701_, 0);
if (lean_obj_tag(v_pre_713_) == 0)
{
lean_object* v_i_714_; lean_object* v___x_715_; 
v_i_714_ = lean_ctor_get(v_n_701_, 1);
lean_inc(v_i_714_);
lean_dec_ref(v_n_701_);
v___x_715_ = l_Nat_reprFast(v_i_714_);
return v___x_715_;
}
else
{
lean_object* v_i_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_inc(v_pre_713_);
v_i_716_ = lean_ctor_get(v_n_701_, 1);
lean_inc(v_i_716_);
lean_dec_ref(v_n_701_);
v___x_717_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_699_, v_escape_700_, v_pre_713_);
v___x_718_ = lean_string_append(v___x_717_, v_sep_699_);
v___x_719_ = l_Nat_reprFast(v_i_716_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_721_, lean_object* v_escape_722_, lean_object* v_n_723_){
_start:
{
uint8_t v_escape_boxed_724_; lean_object* v_res_725_; 
v_escape_boxed_724_ = lean_unbox(v_escape_722_);
v_res_725_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_721_, v_escape_boxed_724_, v_n_723_);
lean_dec_ref(v_sep_721_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_726_, uint8_t v_escape_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_727_ == 0)
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_728_, v_escape_727_, v_n_726_);
return v___x_729_;
}
else
{
uint8_t v___x_730_; 
lean_inc(v_n_726_);
v___x_730_ = lean_is_inaccessible_user_name(v_n_726_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Lean_Name_hasMacroScopes(v_n_726_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
v___x_732_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_726_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_728_, v_escape_727_, v_n_726_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_728_, v___x_731_, v_n_726_);
return v___x_734_;
}
}
else
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_728_, v___x_730_, v_n_726_);
return v___x_735_;
}
}
else
{
uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = 0;
v___x_737_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_728_, v___x_736_, v_n_726_);
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_738_, lean_object* v_escape_739_){
_start:
{
uint8_t v_escape_boxed_740_; lean_object* v_res_741_; 
v_escape_boxed_740_ = lean_unbox(v_escape_739_);
v_res_741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_738_, v_escape_boxed_740_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_742_, uint8_t v_escape_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_742_, v_escape_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_745_, lean_object* v_escape_746_){
_start:
{
uint8_t v_escape_boxed_747_; lean_object* v_res_748_; 
v_escape_boxed_747_ = lean_unbox(v_escape_746_);
v_res_748_ = l_Lean_Name_toString(v_n_745_, v_escape_boxed_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_749_){
_start:
{
uint8_t v___x_750_; lean_object* v___x_751_; 
v___x_750_ = 1;
v___x_751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_749_, v___x_750_);
return v___x_751_;
}
}
lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
