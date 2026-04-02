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
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
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
uint8_t lean_is_inaccessible_user_name(lean_object*);
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
lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v_startInclusive_126_; lean_object* v_endExclusive_127_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; uint8_t v___y_154_; uint32_t v___y_156_; uint8_t v___y_157_; uint32_t v___y_162_; uint32_t v___y_168_; uint8_t v___y_174_; lean_object* v___x_185_; uint8_t v_c_186_; uint8_t v___y_188_; uint8_t v___y_192_; uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v_c_186_ = lean_string_get_byte_fast(v_s_121_, v___x_185_);
v___x_197_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_198_ = lean_uint8_dec_le(v___x_197_, v_c_186_);
if (v___x_198_ == 0)
{
v___y_192_ = v___x_198_;
goto v___jp_191_;
}
else
{
uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_200_ = lean_uint8_dec_le(v_c_186_, v___x_199_);
v___y_192_ = v___x_200_;
goto v___jp_191_;
}
v___jp_122_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
lean_inc_ref(v___y_124_);
v___x_128_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_124_);
lean_inc(v___y_123_);
v___x_129_ = l_String_Slice_Pos_skipWhile___redArg(v___y_125_, v___y_123_, v___x_128_);
lean_dec_ref(v___y_125_);
v___x_130_ = lean_nat_add(v_startInclusive_126_, v___x_129_);
lean_dec(v___x_129_);
lean_dec(v_startInclusive_126_);
v___x_131_ = lean_nat_sub(v_endExclusive_127_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v_endExclusive_127_);
v___x_132_ = lean_nat_dec_eq(v___x_131_, v___y_123_);
lean_dec(v___y_123_);
lean_dec(v___x_131_);
return v___x_132_;
}
v___jp_133_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_startInclusive_139_; lean_object* v_endExclusive_140_; 
v___x_137_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_138_ = l_panic___redArg(v___y_136_, v___x_137_);
v_startInclusive_139_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_startInclusive_139_);
v_endExclusive_140_ = lean_ctor_get(v___x_138_, 2);
lean_inc(v_endExclusive_140_);
v___y_123_ = v___y_134_;
v___y_124_ = v___y_135_;
v___y_125_ = v___x_138_;
v_startInclusive_126_ = v_startInclusive_139_;
v_endExclusive_127_ = v_endExclusive_140_;
goto v___jp_122_;
}
v___jp_141_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_144_, 0, v_s_121_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = l_Substring_Raw_nextn(v___x_144_, v___x_145_, v___x_142_);
lean_dec_ref(v___x_144_);
v___x_147_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_148_ = l_String_instInhabitedSlice;
v___x_149_ = lean_string_is_valid_pos(v_s_121_, v___x_146_);
if (v___x_149_ == 0)
{
lean_dec(v___x_146_);
lean_dec_ref(v_s_121_);
v___y_134_ = v___x_142_;
v___y_135_ = v___x_147_;
v___y_136_ = v___x_148_;
goto v___jp_133_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_string_is_valid_pos(v_s_121_, v___x_143_);
if (v___x_150_ == 0)
{
lean_dec(v___x_146_);
lean_dec_ref(v_s_121_);
v___y_134_ = v___x_142_;
v___y_135_ = v___x_147_;
v___y_136_ = v___x_148_;
goto v___jp_133_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_le(v___x_146_, v___x_143_);
if (v___x_151_ == 0)
{
lean_dec(v___x_146_);
lean_dec_ref(v_s_121_);
v___y_134_ = v___x_142_;
v___y_135_ = v___x_147_;
v___y_136_ = v___x_148_;
goto v___jp_133_;
}
else
{
lean_object* v___x_152_; 
lean_inc(v___x_146_);
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v_s_121_);
lean_ctor_set(v___x_152_, 1, v___x_146_);
lean_ctor_set(v___x_152_, 2, v___x_143_);
v___y_123_ = v___x_142_;
v___y_124_ = v___x_147_;
v___y_125_ = v___x_152_;
v_startInclusive_126_ = v___x_146_;
v_endExclusive_127_ = v___x_143_;
goto v___jp_122_;
}
}
}
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
lean_dec_ref(v_s_121_);
return v___y_154_;
}
else
{
goto v___jp_141_;
}
}
v___jp_155_:
{
if (v___y_157_ == 0)
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 95;
v___x_159_ = lean_uint32_dec_eq(v___y_156_, v___x_158_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_isLetterLike(v___y_156_);
v___y_154_ = v___x_160_;
goto v___jp_153_;
}
else
{
v___y_154_ = v___x_159_;
goto v___jp_153_;
}
}
else
{
goto v___jp_141_;
}
}
v___jp_161_:
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 97;
v___x_164_ = lean_uint32_dec_le(v___x_163_, v___y_162_);
if (v___x_164_ == 0)
{
v___y_156_ = v___y_162_;
v___y_157_ = v___x_164_;
goto v___jp_155_;
}
else
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 122;
v___x_166_ = lean_uint32_dec_le(v___y_162_, v___x_165_);
v___y_156_ = v___y_162_;
v___y_157_ = v___x_166_;
goto v___jp_155_;
}
}
v___jp_167_:
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 65;
v___x_170_ = lean_uint32_dec_le(v___x_169_, v___y_168_);
if (v___x_170_ == 0)
{
v___y_162_ = v___y_168_;
goto v___jp_161_;
}
else
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 90;
v___x_172_ = lean_uint32_dec_le(v___y_168_, v___x_171_);
if (v___x_172_ == 0)
{
v___y_162_ = v___y_168_;
goto v___jp_161_;
}
else
{
goto v___jp_141_;
}
}
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v_s_121_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
v___x_178_ = l_String_Slice_Pos_get_x3f(v___x_177_, v___x_175_);
lean_dec_ref(v___x_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
uint32_t v___x_179_; 
v___x_179_ = 65;
v___y_168_ = v___x_179_;
goto v___jp_167_;
}
else
{
lean_object* v_val_180_; uint32_t v___x_181_; 
v_val_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v___x_178_);
v___x_181_ = lean_unbox_uint32(v_val_180_);
lean_dec(v_val_180_);
v___y_168_ = v___x_181_;
goto v___jp_167_;
}
}
else
{
lean_dec_ref(v_s_121_);
return v___y_174_;
}
}
v___jp_182_:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_121_, v___x_183_);
v___y_174_ = v___x_184_;
goto v___jp_173_;
}
v___jp_187_:
{
if (v___y_188_ == 0)
{
uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_190_ = lean_uint8_dec_eq(v_c_186_, v___x_189_);
if (v___x_190_ == 0)
{
v___y_174_ = v___x_190_;
goto v___jp_173_;
}
else
{
goto v___jp_182_;
}
}
else
{
goto v___jp_182_;
}
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
uint8_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_194_ = lean_uint8_dec_le(v___x_193_, v_c_186_);
if (v___x_194_ == 0)
{
v___y_188_ = v___x_194_;
goto v___jp_187_;
}
else
{
uint8_t v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_196_ = lean_uint8_dec_le(v_c_186_, v___x_195_);
v___y_188_ = v___x_196_;
goto v___jp_187_;
}
}
else
{
goto v___jp_182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_204_, lean_object* v_h_205_){
_start:
{
lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v_startInclusive_210_; lean_object* v_endExclusive_211_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; uint8_t v___y_238_; uint32_t v___y_240_; uint8_t v___y_241_; uint32_t v___y_246_; uint32_t v___y_252_; uint8_t v___y_258_; lean_object* v___x_269_; uint8_t v_c_270_; uint8_t v___y_272_; uint8_t v___y_276_; uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v_c_270_ = lean_string_get_byte_fast(v_s_204_, v___x_269_);
v___x_281_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_282_ = lean_uint8_dec_le(v___x_281_, v_c_270_);
if (v___x_282_ == 0)
{
v___y_276_ = v___x_282_;
goto v___jp_275_;
}
else
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_284_ = lean_uint8_dec_le(v_c_270_, v___x_283_);
v___y_276_ = v___x_284_;
goto v___jp_275_;
}
v___jp_206_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
lean_inc_ref(v___y_208_);
v___x_212_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_208_);
lean_inc(v___y_207_);
v___x_213_ = l_String_Slice_Pos_skipWhile___redArg(v___y_209_, v___y_207_, v___x_212_);
lean_dec_ref(v___y_209_);
v___x_214_ = lean_nat_add(v_startInclusive_210_, v___x_213_);
lean_dec(v___x_213_);
lean_dec(v_startInclusive_210_);
v___x_215_ = lean_nat_sub(v_endExclusive_211_, v___x_214_);
lean_dec(v___x_214_);
lean_dec(v_endExclusive_211_);
v___x_216_ = lean_nat_dec_eq(v___x_215_, v___y_207_);
lean_dec(v___y_207_);
lean_dec(v___x_215_);
return v___x_216_;
}
v___jp_217_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_startInclusive_223_; lean_object* v_endExclusive_224_; 
v___x_221_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_222_ = l_panic___redArg(v___y_220_, v___x_221_);
v_startInclusive_223_ = lean_ctor_get(v___x_222_, 1);
lean_inc(v_startInclusive_223_);
v_endExclusive_224_ = lean_ctor_get(v___x_222_, 2);
lean_inc(v_endExclusive_224_);
v___y_207_ = v___y_218_;
v___y_208_ = v___y_219_;
v___y_209_ = v___x_222_;
v_startInclusive_210_ = v_startInclusive_223_;
v_endExclusive_211_ = v_endExclusive_224_;
goto v___jp_206_;
}
v___jp_225_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_string_utf8_byte_size(v_s_204_);
lean_inc_ref(v_s_204_);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v_s_204_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = l_Substring_Raw_nextn(v___x_228_, v___x_229_, v___x_226_);
lean_dec_ref(v___x_228_);
v___x_231_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_232_ = l_String_instInhabitedSlice;
v___x_233_ = lean_string_is_valid_pos(v_s_204_, v___x_230_);
if (v___x_233_ == 0)
{
lean_dec(v___x_230_);
lean_dec_ref(v_s_204_);
v___y_218_ = v___x_226_;
v___y_219_ = v___x_231_;
v___y_220_ = v___x_232_;
goto v___jp_217_;
}
else
{
uint8_t v___x_234_; 
v___x_234_ = lean_string_is_valid_pos(v_s_204_, v___x_227_);
if (v___x_234_ == 0)
{
lean_dec(v___x_230_);
lean_dec_ref(v_s_204_);
v___y_218_ = v___x_226_;
v___y_219_ = v___x_231_;
v___y_220_ = v___x_232_;
goto v___jp_217_;
}
else
{
uint8_t v___x_235_; 
v___x_235_ = lean_nat_dec_le(v___x_230_, v___x_227_);
if (v___x_235_ == 0)
{
lean_dec(v___x_230_);
lean_dec_ref(v_s_204_);
v___y_218_ = v___x_226_;
v___y_219_ = v___x_231_;
v___y_220_ = v___x_232_;
goto v___jp_217_;
}
else
{
lean_object* v___x_236_; 
lean_inc(v___x_230_);
v___x_236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_236_, 0, v_s_204_);
lean_ctor_set(v___x_236_, 1, v___x_230_);
lean_ctor_set(v___x_236_, 2, v___x_227_);
v___y_207_ = v___x_226_;
v___y_208_ = v___x_231_;
v___y_209_ = v___x_236_;
v_startInclusive_210_ = v___x_230_;
v_endExclusive_211_ = v___x_227_;
goto v___jp_206_;
}
}
}
}
v___jp_237_:
{
if (v___y_238_ == 0)
{
lean_dec_ref(v_s_204_);
return v___y_238_;
}
else
{
goto v___jp_225_;
}
}
v___jp_239_:
{
if (v___y_241_ == 0)
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 95;
v___x_243_ = lean_uint32_dec_eq(v___y_240_, v___x_242_);
if (v___x_243_ == 0)
{
uint8_t v___x_244_; 
v___x_244_ = l_Lean_isLetterLike(v___y_240_);
v___y_238_ = v___x_244_;
goto v___jp_237_;
}
else
{
v___y_238_ = v___x_243_;
goto v___jp_237_;
}
}
else
{
goto v___jp_225_;
}
}
v___jp_245_:
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 97;
v___x_248_ = lean_uint32_dec_le(v___x_247_, v___y_246_);
if (v___x_248_ == 0)
{
v___y_240_ = v___y_246_;
v___y_241_ = v___x_248_;
goto v___jp_239_;
}
else
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 122;
v___x_250_ = lean_uint32_dec_le(v___y_246_, v___x_249_);
v___y_240_ = v___y_246_;
v___y_241_ = v___x_250_;
goto v___jp_239_;
}
}
v___jp_251_:
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 65;
v___x_254_ = lean_uint32_dec_le(v___x_253_, v___y_252_);
if (v___x_254_ == 0)
{
v___y_246_ = v___y_252_;
goto v___jp_245_;
}
else
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 90;
v___x_256_ = lean_uint32_dec_le(v___y_252_, v___x_255_);
if (v___x_256_ == 0)
{
v___y_246_ = v___y_252_;
goto v___jp_245_;
}
else
{
goto v___jp_225_;
}
}
}
v___jp_257_:
{
if (v___y_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_string_utf8_byte_size(v_s_204_);
lean_inc_ref(v_s_204_);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v_s_204_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
v___x_262_ = l_String_Slice_Pos_get_x3f(v___x_261_, v___x_259_);
lean_dec_ref(v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
uint32_t v___x_263_; 
v___x_263_ = 65;
v___y_252_ = v___x_263_;
goto v___jp_251_;
}
else
{
lean_object* v_val_264_; uint32_t v___x_265_; 
v_val_264_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_val_264_);
lean_dec_ref(v___x_262_);
v___x_265_ = lean_unbox_uint32(v_val_264_);
lean_dec(v_val_264_);
v___y_252_ = v___x_265_;
goto v___jp_251_;
}
}
else
{
lean_dec_ref(v_s_204_);
return v___y_258_;
}
}
v___jp_266_:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_204_, v___x_267_);
v___y_258_ = v___x_268_;
goto v___jp_257_;
}
v___jp_271_:
{
if (v___y_272_ == 0)
{
uint8_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_274_ = lean_uint8_dec_eq(v_c_270_, v___x_273_);
if (v___x_274_ == 0)
{
v___y_258_ = v___x_274_;
goto v___jp_257_;
}
else
{
goto v___jp_266_;
}
}
else
{
goto v___jp_266_;
}
}
v___jp_275_:
{
if (v___y_276_ == 0)
{
uint8_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_278_ = lean_uint8_dec_le(v___x_277_, v_c_270_);
if (v___x_278_ == 0)
{
v___y_272_ = v___x_278_;
goto v___jp_271_;
}
else
{
uint8_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_280_ = lean_uint8_dec_le(v_c_270_, v___x_279_);
v___y_272_ = v___x_280_;
goto v___jp_271_;
}
}
else
{
goto v___jp_266_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_285_, lean_object* v_h_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_285_, v_h_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = l_Lean_idBeginEscape;
v___x_291_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_292_ = lean_string_push(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = l_Lean_idEndEscape;
v___x_294_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_295_ = lean_string_push(v___x_294_, v___x_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_298_ = lean_string_append(v___x_297_, v_s_296_);
v___x_299_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_301_);
lean_dec_ref(v_s_301_);
return v_res_302_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_305_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_314_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_306_, v___x_313_, v___y_307_, lean_box(0), lean_box(0), v___y_310_, v___y_311_, v___y_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_318_, uint8_t v_force_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_string_utf8_byte_size(v_s_318_);
v___x_322_ = lean_nat_dec_lt(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_323_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_324_ = lean_string_append(v___x_323_, v_s_318_);
lean_dec_ref(v_s_318_);
v___x_325_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
else
{
lean_object* v___f_328_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v_startInclusive_343_; lean_object* v_endExclusive_344_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; uint8_t v___y_370_; uint32_t v___y_372_; uint8_t v___y_373_; uint32_t v___y_378_; uint32_t v___y_384_; uint8_t v___y_390_; 
v___f_328_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_319_ == 0)
{
uint8_t v_c_400_; uint8_t v___y_402_; uint8_t v___y_406_; uint8_t v___x_411_; uint8_t v___x_412_; 
v_c_400_ = lean_string_get_byte_fast(v_s_318_, v___x_320_);
v___x_411_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_412_ = lean_uint8_dec_le(v___x_411_, v_c_400_);
if (v___x_412_ == 0)
{
v___y_406_ = v___x_412_;
goto v___jp_405_;
}
else
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_414_ = lean_uint8_dec_le(v_c_400_, v___x_413_);
v___y_406_ = v___x_414_;
goto v___jp_405_;
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_404_ = lean_uint8_dec_eq(v_c_400_, v___x_403_);
if (v___x_404_ == 0)
{
v___y_390_ = v___x_404_;
goto v___jp_389_;
}
else
{
goto v___jp_397_;
}
}
else
{
goto v___jp_397_;
}
}
v___jp_405_:
{
if (v___y_406_ == 0)
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_408_ = lean_uint8_dec_le(v___x_407_, v_c_400_);
if (v___x_408_ == 0)
{
v___y_402_ = v___x_408_;
goto v___jp_401_;
}
else
{
uint8_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_410_ = lean_uint8_dec_le(v_c_400_, v___x_409_);
v___y_402_ = v___x_410_;
goto v___jp_401_;
}
}
else
{
goto v___jp_397_;
}
}
}
else
{
goto v___jp_329_;
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_318_);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v_s_318_);
lean_ctor_set(v___x_331_, 1, v___x_320_);
lean_ctor_set(v___x_331_, 2, v___x_321_);
v___x_332_ = l_String_Slice_contains___redArg(v___f_328_, v___x_331_, v___x_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_333_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_334_ = lean_string_append(v___x_333_, v_s_318_);
lean_dec_ref(v_s_318_);
v___x_335_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; 
lean_dec_ref(v_s_318_);
v___x_338_ = lean_box(0);
return v___x_338_;
}
}
v___jp_339_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
lean_inc_ref(v___y_340_);
v___x_345_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_340_);
lean_inc(v___y_341_);
v___x_346_ = l_String_Slice_Pos_skipWhile___redArg(v___y_342_, v___y_341_, v___x_345_);
lean_dec_ref(v___y_342_);
v___x_347_ = lean_nat_add(v_startInclusive_343_, v___x_346_);
lean_dec(v___x_346_);
lean_dec(v_startInclusive_343_);
v___x_348_ = lean_nat_sub(v_endExclusive_344_, v___x_347_);
lean_dec(v___x_347_);
lean_dec(v_endExclusive_344_);
v___x_349_ = lean_nat_dec_eq(v___x_348_, v___y_341_);
lean_dec(v___y_341_);
lean_dec(v___x_348_);
if (v___x_349_ == 0)
{
goto v___jp_329_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_s_318_);
return v___x_350_;
}
}
v___jp_351_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_startInclusive_357_; lean_object* v_endExclusive_358_; 
v___x_355_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_356_ = l_panic___redArg(v___y_352_, v___x_355_);
v_startInclusive_357_ = lean_ctor_get(v___x_356_, 1);
lean_inc(v_startInclusive_357_);
v_endExclusive_358_ = lean_ctor_get(v___x_356_, 2);
lean_inc(v_endExclusive_358_);
v___y_340_ = v___y_353_;
v___y_341_ = v___y_354_;
v___y_342_ = v___x_356_;
v_startInclusive_343_ = v_startInclusive_357_;
v_endExclusive_344_ = v_endExclusive_358_;
goto v___jp_339_;
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
lean_inc_ref(v_s_318_);
v___x_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_360_, 0, v_s_318_);
lean_ctor_set(v___x_360_, 1, v___x_320_);
lean_ctor_set(v___x_360_, 2, v___x_321_);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = l_Substring_Raw_nextn(v___x_360_, v___x_361_, v___x_320_);
lean_dec_ref(v___x_360_);
v___x_363_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_364_ = l_String_instInhabitedSlice;
v___x_365_ = lean_string_is_valid_pos(v_s_318_, v___x_362_);
if (v___x_365_ == 0)
{
lean_dec(v___x_362_);
v___y_352_ = v___x_364_;
v___y_353_ = v___x_363_;
v___y_354_ = v___x_320_;
goto v___jp_351_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = lean_string_is_valid_pos(v_s_318_, v___x_321_);
if (v___x_366_ == 0)
{
lean_dec(v___x_362_);
v___y_352_ = v___x_364_;
v___y_353_ = v___x_363_;
v___y_354_ = v___x_320_;
goto v___jp_351_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_le(v___x_362_, v___x_321_);
if (v___x_367_ == 0)
{
lean_dec(v___x_362_);
v___y_352_ = v___x_364_;
v___y_353_ = v___x_363_;
v___y_354_ = v___x_320_;
goto v___jp_351_;
}
else
{
lean_object* v___x_368_; 
lean_inc(v___x_362_);
lean_inc_ref(v_s_318_);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v_s_318_);
lean_ctor_set(v___x_368_, 1, v___x_362_);
lean_ctor_set(v___x_368_, 2, v___x_321_);
v___y_340_ = v___x_363_;
v___y_341_ = v___x_320_;
v___y_342_ = v___x_368_;
v_startInclusive_343_ = v___x_362_;
v_endExclusive_344_ = v___x_321_;
goto v___jp_339_;
}
}
}
}
v___jp_369_:
{
if (v___y_370_ == 0)
{
goto v___jp_329_;
}
else
{
goto v___jp_359_;
}
}
v___jp_371_:
{
if (v___y_373_ == 0)
{
uint32_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 95;
v___x_375_ = lean_uint32_dec_eq(v___y_372_, v___x_374_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_isLetterLike(v___y_372_);
v___y_370_ = v___x_376_;
goto v___jp_369_;
}
else
{
v___y_370_ = v___x_375_;
goto v___jp_369_;
}
}
else
{
goto v___jp_359_;
}
}
v___jp_377_:
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 97;
v___x_380_ = lean_uint32_dec_le(v___x_379_, v___y_378_);
if (v___x_380_ == 0)
{
v___y_372_ = v___y_378_;
v___y_373_ = v___x_380_;
goto v___jp_371_;
}
else
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 122;
v___x_382_ = lean_uint32_dec_le(v___y_378_, v___x_381_);
v___y_372_ = v___y_378_;
v___y_373_ = v___x_382_;
goto v___jp_371_;
}
}
v___jp_383_:
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 65;
v___x_386_ = lean_uint32_dec_le(v___x_385_, v___y_384_);
if (v___x_386_ == 0)
{
v___y_378_ = v___y_384_;
goto v___jp_377_;
}
else
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 90;
v___x_388_ = lean_uint32_dec_le(v___y_384_, v___x_387_);
if (v___x_388_ == 0)
{
v___y_378_ = v___y_384_;
goto v___jp_377_;
}
else
{
goto v___jp_359_;
}
}
}
v___jp_389_:
{
if (v___y_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc_ref(v_s_318_);
v___x_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_391_, 0, v_s_318_);
lean_ctor_set(v___x_391_, 1, v___x_320_);
lean_ctor_set(v___x_391_, 2, v___x_321_);
v___x_392_ = l_String_Slice_Pos_get_x3f(v___x_391_, v___x_320_);
lean_dec_ref(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
uint32_t v___x_393_; 
v___x_393_ = 65;
v___y_384_ = v___x_393_;
goto v___jp_383_;
}
else
{
lean_object* v_val_394_; uint32_t v___x_395_; 
v_val_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_394_);
lean_dec_ref(v___x_392_);
v___x_395_ = lean_unbox_uint32(v_val_394_);
lean_dec(v_val_394_);
v___y_384_ = v___x_395_;
goto v___jp_383_;
}
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_s_318_);
return v___x_396_;
}
}
v___jp_397_:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_318_, v___x_398_);
v___y_390_ = v___x_399_;
goto v___jp_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_415_, lean_object* v_force_416_){
_start:
{
uint8_t v_force_boxed_417_; lean_object* v_res_418_; 
v_force_boxed_417_ = lean_unbox(v_force_416_);
v_res_418_ = l_Lean_Name_escapePart(v_s_415_, v_force_boxed_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = l_String_instInhabitedSlice;
v___x_421_ = lean_panic_fn_borrowed(v___x_420_, v_msg_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_422_, lean_object* v_pos_423_){
_start:
{
lean_object* v_str_424_; lean_object* v_startInclusive_425_; lean_object* v_endExclusive_426_; lean_object* v___x_427_; uint8_t v___y_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_str_424_ = lean_ctor_get(v_s_422_, 0);
v_startInclusive_425_ = lean_ctor_get(v_s_422_, 1);
v_endExclusive_426_ = lean_ctor_get(v_s_422_, 2);
v___x_427_ = lean_nat_add(v_startInclusive_425_, v_pos_423_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_sub(v_endExclusive_426_, v___x_427_);
v___x_438_ = lean_nat_dec_eq(v___x_436_, v___x_437_);
lean_dec(v___x_437_);
if (v___x_438_ == 0)
{
uint32_t v___x_439_; uint8_t v___y_441_; uint8_t v___y_453_; uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_439_ = lean_string_utf8_get_fast(v_str_424_, v___x_427_);
v___x_463_ = 65;
v___x_464_ = lean_uint32_dec_le(v___x_463_, v___x_439_);
if (v___x_464_ == 0)
{
goto v___jp_458_;
}
else
{
uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 90;
v___x_466_ = lean_uint32_dec_le(v___x_439_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_458_;
}
else
{
goto v___jp_428_;
}
}
v___jp_440_:
{
if (v___y_441_ == 0)
{
uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 95;
v___x_443_ = lean_uint32_dec_eq(v___x_439_, v___x_442_);
if (v___x_443_ == 0)
{
uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = 39;
v___x_445_ = lean_uint32_dec_eq(v___x_439_, v___x_444_);
if (v___x_445_ == 0)
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 33;
v___x_447_ = lean_uint32_dec_eq(v___x_439_, v___x_446_);
if (v___x_447_ == 0)
{
uint32_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = 63;
v___x_449_ = lean_uint32_dec_eq(v___x_439_, v___x_448_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
v___x_450_ = l_Lean_isLetterLike(v___x_439_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_isSubScriptAlnum(v___x_439_);
v___y_435_ = v___x_451_;
goto v___jp_434_;
}
else
{
v___y_435_ = v___x_450_;
goto v___jp_434_;
}
}
else
{
v___y_435_ = v___x_449_;
goto v___jp_434_;
}
}
else
{
v___y_435_ = v___x_447_;
goto v___jp_434_;
}
}
else
{
v___y_435_ = v___x_445_;
goto v___jp_434_;
}
}
else
{
v___y_435_ = v___x_443_;
goto v___jp_434_;
}
}
else
{
goto v___jp_428_;
}
}
v___jp_452_:
{
if (v___y_453_ == 0)
{
uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_454_ = 48;
v___x_455_ = lean_uint32_dec_le(v___x_454_, v___x_439_);
if (v___x_455_ == 0)
{
v___y_441_ = v___x_455_;
goto v___jp_440_;
}
else
{
uint32_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 57;
v___x_457_ = lean_uint32_dec_le(v___x_439_, v___x_456_);
v___y_441_ = v___x_457_;
goto v___jp_440_;
}
}
else
{
goto v___jp_428_;
}
}
v___jp_458_:
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 97;
v___x_460_ = lean_uint32_dec_le(v___x_459_, v___x_439_);
if (v___x_460_ == 0)
{
v___y_453_ = v___x_460_;
goto v___jp_452_;
}
else
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 122;
v___x_462_ = lean_uint32_dec_le(v___x_439_, v___x_461_);
v___y_453_ = v___x_462_;
goto v___jp_452_;
}
}
}
else
{
lean_dec(v___x_427_);
return v_pos_423_;
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_429_ = lean_string_utf8_next_fast(v_str_424_, v___x_427_);
v___x_430_ = lean_nat_sub(v___x_429_, v___x_427_);
lean_dec(v___x_427_);
v___x_431_ = lean_nat_add(v_pos_423_, v___x_430_);
lean_dec(v___x_430_);
v___x_432_ = l_String_instDecidableLtRaw___aux__1(v_pos_423_, v___x_431_);
if (v___x_432_ == 0)
{
lean_dec(v___x_431_);
return v_pos_423_;
}
else
{
lean_dec(v_pos_423_);
v_pos_423_ = v___x_431_;
goto _start;
}
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
lean_dec(v___x_427_);
return v_pos_423_;
}
else
{
goto v___jp_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_467_, lean_object* v_pos_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_467_, v_pos_468_);
lean_dec_ref(v_s_467_);
return v_res_469_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_470_, lean_object* v_a_471_, uint8_t v_b_472_){
_start:
{
lean_object* v_str_473_; lean_object* v_startInclusive_474_; lean_object* v_endExclusive_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_str_473_ = lean_ctor_get(v_s_470_, 0);
v_startInclusive_474_ = lean_ctor_get(v_s_470_, 1);
v_endExclusive_475_ = lean_ctor_get(v_s_470_, 2);
v___x_476_ = lean_nat_sub(v_endExclusive_475_, v_startInclusive_474_);
v___x_477_ = lean_nat_dec_eq(v_a_471_, v___x_476_);
lean_dec(v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint32_t v___x_479_; uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_478_ = lean_nat_add(v_startInclusive_474_, v_a_471_);
lean_dec(v_a_471_);
v___x_479_ = lean_string_utf8_get_fast(v_str_473_, v___x_478_);
v___x_480_ = 187;
v___x_481_ = lean_uint32_dec_eq(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_string_utf8_next_fast(v_str_473_, v___x_478_);
lean_dec(v___x_478_);
v___x_483_ = lean_nat_sub(v___x_482_, v_startInclusive_474_);
v_a_471_ = v___x_483_;
v_b_472_ = v___x_481_;
goto _start;
}
else
{
lean_dec(v___x_478_);
return v___x_481_;
}
}
else
{
lean_dec(v_a_471_);
return v_b_472_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_485_, lean_object* v_a_486_, lean_object* v_b_487_){
_start:
{
uint8_t v_b_boxed_488_; uint8_t v_res_489_; lean_object* v_r_490_; 
v_b_boxed_488_ = lean_unbox(v_b_487_);
v_res_489_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_485_, v_a_486_, v_b_boxed_488_);
lean_dec_ref(v_s_485_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_491_){
_start:
{
lean_object* v_searcher_492_; uint8_t v___x_493_; uint8_t v___x_494_; 
v_searcher_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = 0;
v___x_494_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_491_, v_searcher_492_, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_495_);
lean_dec_ref(v_s_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_498_, lean_object* v_s_499_, uint8_t v_force_500_){
_start:
{
lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v_startInclusive_513_; lean_object* v_endExclusive_514_; lean_object* v___y_520_; uint8_t v___y_536_; uint32_t v___y_538_; uint8_t v___y_539_; uint32_t v___y_544_; uint32_t v___y_550_; uint8_t v___y_556_; 
if (v_escape_498_ == 0)
{
return v_s_499_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_string_utf8_byte_size(v_s_499_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_571_ = lean_string_append(v___x_570_, v_s_499_);
lean_dec_ref(v_s_499_);
v___x_572_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_573_ = lean_string_append(v___x_571_, v___x_572_);
return v___x_573_;
}
else
{
if (v_force_500_ == 0)
{
uint8_t v_c_574_; uint8_t v___y_576_; uint8_t v___y_580_; uint8_t v___x_585_; uint8_t v___x_586_; 
v_c_574_ = lean_string_get_byte_fast(v_s_499_, v___x_567_);
v___x_585_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_586_ = lean_uint8_dec_le(v___x_585_, v_c_574_);
if (v___x_586_ == 0)
{
v___y_580_ = v___x_586_;
goto v___jp_579_;
}
else
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_588_ = lean_uint8_dec_le(v_c_574_, v___x_587_);
v___y_580_ = v___x_588_;
goto v___jp_579_;
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
uint8_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_578_ = lean_uint8_dec_eq(v_c_574_, v___x_577_);
if (v___x_578_ == 0)
{
v___y_556_ = v___x_578_;
goto v___jp_555_;
}
else
{
goto v___jp_564_;
}
}
else
{
goto v___jp_564_;
}
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
uint8_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_582_ = lean_uint8_dec_le(v___x_581_, v_c_574_);
if (v___x_582_ == 0)
{
v___y_576_ = v___x_582_;
goto v___jp_575_;
}
else
{
uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_584_ = lean_uint8_dec_le(v_c_574_, v___x_583_);
v___y_576_ = v___x_584_;
goto v___jp_575_;
}
}
else
{
goto v___jp_564_;
}
}
}
else
{
goto v___jp_501_;
}
}
}
v___jp_501_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_string_utf8_byte_size(v_s_499_);
lean_inc_ref(v_s_499_);
v___x_504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_504_, 0, v_s_499_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
lean_ctor_set(v___x_504_, 2, v___x_503_);
v___x_505_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_504_);
lean_dec_ref(v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_507_ = lean_string_append(v___x_506_, v_s_499_);
lean_dec_ref(v_s_499_);
v___x_508_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
return v___x_509_;
}
else
{
return v_s_499_;
}
}
v___jp_510_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
lean_inc(v___y_511_);
v___x_515_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_512_, v___y_511_);
lean_dec_ref(v___y_512_);
v___x_516_ = lean_nat_add(v_startInclusive_513_, v___x_515_);
lean_dec(v___x_515_);
lean_dec(v_startInclusive_513_);
v___x_517_ = lean_nat_sub(v_endExclusive_514_, v___x_516_);
lean_dec(v___x_516_);
lean_dec(v_endExclusive_514_);
v___x_518_ = lean_nat_dec_eq(v___x_517_, v___y_511_);
lean_dec(v___y_511_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
goto v___jp_501_;
}
else
{
return v_s_499_;
}
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
v___y_511_ = v___y_520_;
v___y_512_ = v___x_522_;
v_startInclusive_513_ = v_startInclusive_523_;
v_endExclusive_514_ = v_endExclusive_524_;
goto v___jp_510_;
}
v___jp_525_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_string_utf8_byte_size(v_s_499_);
lean_inc_ref(v_s_499_);
v___x_528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_528_, 0, v_s_499_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = l_Substring_Raw_nextn(v___x_528_, v___x_529_, v___x_526_);
lean_dec_ref(v___x_528_);
v___x_531_ = lean_string_is_valid_pos(v_s_499_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec(v___x_530_);
v___y_520_ = v___x_526_;
goto v___jp_519_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = lean_string_is_valid_pos(v_s_499_, v___x_527_);
if (v___x_532_ == 0)
{
lean_dec(v___x_530_);
v___y_520_ = v___x_526_;
goto v___jp_519_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_le(v___x_530_, v___x_527_);
if (v___x_533_ == 0)
{
lean_dec(v___x_530_);
v___y_520_ = v___x_526_;
goto v___jp_519_;
}
else
{
lean_object* v___x_534_; 
lean_inc(v___x_530_);
lean_inc_ref(v_s_499_);
v___x_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_534_, 0, v_s_499_);
lean_ctor_set(v___x_534_, 1, v___x_530_);
lean_ctor_set(v___x_534_, 2, v___x_527_);
v___y_511_ = v___x_526_;
v___y_512_ = v___x_534_;
v_startInclusive_513_ = v___x_530_;
v_endExclusive_514_ = v___x_527_;
goto v___jp_510_;
}
}
}
}
v___jp_535_:
{
if (v___y_536_ == 0)
{
goto v___jp_501_;
}
else
{
goto v___jp_525_;
}
}
v___jp_537_:
{
if (v___y_539_ == 0)
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 95;
v___x_541_ = lean_uint32_dec_eq(v___y_538_, v___x_540_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_isLetterLike(v___y_538_);
v___y_536_ = v___x_542_;
goto v___jp_535_;
}
else
{
v___y_536_ = v___x_541_;
goto v___jp_535_;
}
}
else
{
goto v___jp_525_;
}
}
v___jp_543_:
{
uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = 97;
v___x_546_ = lean_uint32_dec_le(v___x_545_, v___y_544_);
if (v___x_546_ == 0)
{
v___y_538_ = v___y_544_;
v___y_539_ = v___x_546_;
goto v___jp_537_;
}
else
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 122;
v___x_548_ = lean_uint32_dec_le(v___y_544_, v___x_547_);
v___y_538_ = v___y_544_;
v___y_539_ = v___x_548_;
goto v___jp_537_;
}
}
v___jp_549_:
{
uint32_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 65;
v___x_552_ = lean_uint32_dec_le(v___x_551_, v___y_550_);
if (v___x_552_ == 0)
{
v___y_544_ = v___y_550_;
goto v___jp_543_;
}
else
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 90;
v___x_554_ = lean_uint32_dec_le(v___y_550_, v___x_553_);
if (v___x_554_ == 0)
{
v___y_544_ = v___y_550_;
goto v___jp_543_;
}
else
{
goto v___jp_525_;
}
}
}
v___jp_555_:
{
if (v___y_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_string_utf8_byte_size(v_s_499_);
lean_inc_ref(v_s_499_);
v___x_559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_559_, 0, v_s_499_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
v___x_560_ = l_String_Slice_Pos_get_x3f(v___x_559_, v___x_557_);
lean_dec_ref(v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
uint32_t v___x_561_; 
v___x_561_ = 65;
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
else
{
lean_object* v_val_562_; uint32_t v___x_563_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_562_);
lean_dec_ref(v___x_560_);
v___x_563_ = lean_unbox_uint32(v_val_562_);
lean_dec(v_val_562_);
v___y_550_ = v___x_563_;
goto v___jp_549_;
}
}
else
{
return v_s_499_;
}
}
v___jp_564_:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_499_, v___x_565_);
v___y_556_ = v___x_566_;
goto v___jp_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_589_, lean_object* v_s_590_, lean_object* v_force_591_){
_start:
{
uint8_t v_escape_boxed_592_; uint8_t v_force_boxed_593_; lean_object* v_res_594_; 
v_escape_boxed_592_ = lean_unbox(v_escape_589_);
v_force_boxed_593_ = lean_unbox(v_force_591_);
v_res_594_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_592_, v_s_590_, v_force_boxed_593_);
return v_res_594_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_595_, lean_object* v_inst_596_, lean_object* v_R_597_, lean_object* v_a_598_, uint8_t v_b_599_, lean_object* v_c_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_595_, v_a_598_, v_b_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_602_, lean_object* v_inst_603_, lean_object* v_R_604_, lean_object* v_a_605_, lean_object* v_b_606_, lean_object* v_c_607_){
_start:
{
uint8_t v_b_boxed_608_; uint8_t v_res_609_; lean_object* v_r_610_; 
v_b_boxed_608_ = lean_unbox(v_b_606_);
v_res_609_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_602_, v_inst_603_, v_R_604_, v_a_605_, v_b_boxed_608_, v_c_607_);
lean_dec_ref(v_s_602_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_Name_toStringWithSep___lam__0(v_x_613_);
lean_dec_ref(v_x_613_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_618_, uint8_t v_escape_619_, lean_object* v_n_620_, lean_object* v_isToken_621_){
_start:
{
switch(lean_obj_tag(v_n_620_))
{
case 0:
{
lean_object* v___x_622_; 
lean_dec_ref(v_isToken_621_);
v___x_622_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_622_;
}
case 1:
{
lean_object* v_pre_623_; 
v_pre_623_ = lean_ctor_get(v_n_620_, 0);
if (lean_obj_tag(v_pre_623_) == 0)
{
lean_object* v_str_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; 
v_str_624_ = lean_ctor_get(v_n_620_, 1);
lean_inc_ref_n(v_str_624_, 2);
lean_dec_ref(v_n_620_);
v___x_625_ = lean_apply_1(v_isToken_621_, v_str_624_);
v___x_626_ = lean_unbox(v___x_625_);
v___x_627_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_619_, v_str_624_, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v_str_628_; lean_object* v_r_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v_r_x27_633_; 
lean_inc(v_pre_623_);
v_str_628_ = lean_ctor_get(v_n_620_, 1);
lean_inc_ref_n(v_str_628_, 2);
lean_dec_ref(v_n_620_);
lean_inc_ref(v_isToken_621_);
v_r_629_ = l_Lean_Name_toStringWithSep(v_sep_618_, v_escape_619_, v_pre_623_, v_isToken_621_);
v___x_630_ = lean_string_append(v_r_629_, v_sep_618_);
v___x_631_ = 0;
v___x_632_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_619_, v_str_628_, v___x_631_);
lean_inc_ref(v___x_630_);
v_r_x27_633_ = lean_string_append(v___x_630_, v___x_632_);
lean_dec_ref(v___x_632_);
if (v_escape_619_ == 0)
{
lean_dec_ref(v___x_630_);
lean_dec_ref(v_str_628_);
lean_dec_ref(v_isToken_621_);
return v_r_x27_633_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
lean_inc_ref(v_r_x27_633_);
v___x_634_ = lean_apply_1(v_isToken_621_, v_r_x27_633_);
v___x_635_ = lean_unbox(v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v___x_630_);
lean_dec_ref(v_str_628_);
return v_r_x27_633_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec_ref(v_r_x27_633_);
v___x_636_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_619_, v_str_628_, v_escape_619_);
v___x_637_ = lean_string_append(v___x_630_, v___x_636_);
lean_dec_ref(v___x_636_);
return v___x_637_;
}
}
}
}
default: 
{
lean_object* v_pre_638_; 
lean_dec_ref(v_isToken_621_);
v_pre_638_ = lean_ctor_get(v_n_620_, 0);
if (lean_obj_tag(v_pre_638_) == 0)
{
lean_object* v_i_639_; lean_object* v___x_640_; 
v_i_639_ = lean_ctor_get(v_n_620_, 1);
lean_inc(v_i_639_);
lean_dec_ref(v_n_620_);
v___x_640_ = l_Nat_reprFast(v_i_639_);
return v___x_640_;
}
else
{
lean_object* v_i_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc(v_pre_638_);
v_i_641_ = lean_ctor_get(v_n_620_, 1);
lean_inc(v_i_641_);
lean_dec_ref(v_n_620_);
v___f_642_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_643_ = l_Lean_Name_toStringWithSep(v_sep_618_, v_escape_619_, v_pre_638_, v___f_642_);
v___x_644_ = lean_string_append(v___x_643_, v_sep_618_);
v___x_645_ = l_Nat_reprFast(v_i_641_);
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
lean_dec_ref(v___x_645_);
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_647_, lean_object* v_escape_648_, lean_object* v_n_649_, lean_object* v_isToken_650_){
_start:
{
uint8_t v_escape_boxed_651_; lean_object* v_res_652_; 
v_escape_boxed_651_ = lean_unbox(v_escape_648_);
v_res_652_ = l_Lean_Name_toStringWithSep(v_sep_647_, v_escape_boxed_651_, v_n_649_, v_isToken_650_);
lean_dec_ref(v_sep_647_);
return v_res_652_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_658_ = lean_string_utf8_byte_size(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_661_ = lean_string_utf8_byte_size(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_662_){
_start:
{
lean_object* v___x_663_; uint8_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_664_ = lean_name_eq(v_n_662_, v___x_663_);
v___x_665_ = 1;
if (v___x_664_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Name_getRoot(v_n_662_);
if (lean_obj_tag(v___x_666_) == 1)
{
lean_object* v_str_667_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_str_667_ = lean_ctor_get(v___x_666_, 1);
lean_inc_ref(v_str_667_);
lean_dec_ref(v___x_666_);
v___x_675_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_676_ = lean_string_utf8_byte_size(v_str_667_);
v___x_677_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5);
v___x_678_ = lean_nat_dec_le(v___x_677_, v___x_676_);
if (v___x_678_ == 0)
{
goto v___jp_668_;
}
else
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_string_memcmp(v_str_667_, v___x_675_, v___x_679_, v___x_679_, v___x_677_);
if (v___x_680_ == 0)
{
goto v___jp_668_;
}
else
{
lean_dec_ref(v_str_667_);
return v___x_665_;
}
}
v___jp_668_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_669_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_670_ = lean_string_utf8_byte_size(v_str_667_);
v___x_671_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3);
v___x_672_ = lean_nat_dec_le(v___x_671_, v___x_670_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_str_667_);
return v___x_664_;
}
else
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_string_memcmp(v_str_667_, v___x_669_, v___x_673_, v___x_673_, v___x_671_);
lean_dec_ref(v_str_667_);
return v___x_674_;
}
}
}
else
{
lean_dec(v___x_666_);
return v___x_664_;
}
}
else
{
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_681_){
_start:
{
uint8_t v_res_682_; lean_object* v_r_683_; 
v_res_682_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_681_);
lean_dec(v_n_681_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_685_, uint8_t v_escape_686_, lean_object* v_isToken_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_686_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Name_toStringWithSep(v___x_688_, v_escape_686_, v_n_685_, v_isToken_687_);
return v___x_689_;
}
else
{
uint8_t v___x_690_; 
lean_inc(v_n_685_);
v___x_690_ = lean_is_inaccessible_user_name(v_n_685_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_Name_hasMacroScopes(v_n_685_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; 
v___x_692_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_685_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Name_toStringWithSep(v___x_688_, v_escape_686_, v_n_685_, v_isToken_687_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Name_toStringWithSep(v___x_688_, v___x_691_, v_n_685_, v_isToken_687_);
return v___x_694_;
}
}
else
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Name_toStringWithSep(v___x_688_, v___x_690_, v_n_685_, v_isToken_687_);
return v___x_695_;
}
}
else
{
uint8_t v___x_696_; lean_object* v___x_697_; 
v___x_696_ = 0;
v___x_697_ = l_Lean_Name_toStringWithSep(v___x_688_, v___x_696_, v_n_685_, v_isToken_687_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_698_, lean_object* v_escape_699_, lean_object* v_isToken_700_){
_start:
{
uint8_t v_escape_boxed_701_; lean_object* v_res_702_; 
v_escape_boxed_701_ = lean_unbox(v_escape_699_);
v_res_702_ = l_Lean_Name_toStringWithToken(v_n_698_, v_escape_boxed_701_, v_isToken_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_703_, uint8_t v_escape_704_, lean_object* v_n_705_){
_start:
{
switch(lean_obj_tag(v_n_705_))
{
case 0:
{
lean_object* v___x_706_; 
v___x_706_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_706_;
}
case 1:
{
lean_object* v_pre_707_; 
v_pre_707_ = lean_ctor_get(v_n_705_, 0);
if (lean_obj_tag(v_pre_707_) == 0)
{
lean_object* v_str_708_; uint8_t v___x_709_; lean_object* v___x_710_; 
v_str_708_ = lean_ctor_get(v_n_705_, 1);
lean_inc_ref(v_str_708_);
lean_dec_ref(v_n_705_);
v___x_709_ = 0;
v___x_710_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_704_, v_str_708_, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v_str_711_; lean_object* v_r_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v_r_x27_716_; 
lean_inc(v_pre_707_);
v_str_711_ = lean_ctor_get(v_n_705_, 1);
lean_inc_ref(v_str_711_);
lean_dec_ref(v_n_705_);
v_r_712_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_703_, v_escape_704_, v_pre_707_);
v___x_713_ = lean_string_append(v_r_712_, v_sep_703_);
v___x_714_ = 0;
v___x_715_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_704_, v_str_711_, v___x_714_);
v_r_x27_716_ = lean_string_append(v___x_713_, v___x_715_);
lean_dec_ref(v___x_715_);
return v_r_x27_716_;
}
}
default: 
{
lean_object* v_pre_717_; 
v_pre_717_ = lean_ctor_get(v_n_705_, 0);
if (lean_obj_tag(v_pre_717_) == 0)
{
lean_object* v_i_718_; lean_object* v___x_719_; 
v_i_718_ = lean_ctor_get(v_n_705_, 1);
lean_inc(v_i_718_);
lean_dec_ref(v_n_705_);
v___x_719_ = l_Nat_reprFast(v_i_718_);
return v___x_719_;
}
else
{
lean_object* v_i_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_inc(v_pre_717_);
v_i_720_ = lean_ctor_get(v_n_705_, 1);
lean_inc(v_i_720_);
lean_dec_ref(v_n_705_);
v___x_721_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_703_, v_escape_704_, v_pre_717_);
v___x_722_ = lean_string_append(v___x_721_, v_sep_703_);
v___x_723_ = l_Nat_reprFast(v_i_720_);
v___x_724_ = lean_string_append(v___x_722_, v___x_723_);
lean_dec_ref(v___x_723_);
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_725_, lean_object* v_escape_726_, lean_object* v_n_727_){
_start:
{
uint8_t v_escape_boxed_728_; lean_object* v_res_729_; 
v_escape_boxed_728_ = lean_unbox(v_escape_726_);
v_res_729_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_725_, v_escape_boxed_728_, v_n_727_);
lean_dec_ref(v_sep_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_730_, uint8_t v_escape_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_731_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_732_, v_escape_731_, v_n_730_);
return v___x_733_;
}
else
{
uint8_t v___x_734_; 
lean_inc(v_n_730_);
v___x_734_ = lean_is_inaccessible_user_name(v_n_730_);
if (v___x_734_ == 0)
{
uint8_t v___x_735_; 
v___x_735_ = l_Lean_Name_hasMacroScopes(v_n_730_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
v___x_736_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_730_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_732_, v_escape_731_, v_n_730_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_732_, v___x_735_, v_n_730_);
return v___x_738_;
}
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_732_, v___x_734_, v_n_730_);
return v___x_739_;
}
}
else
{
uint8_t v___x_740_; lean_object* v___x_741_; 
v___x_740_ = 0;
v___x_741_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_732_, v___x_740_, v_n_730_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_742_, lean_object* v_escape_743_){
_start:
{
uint8_t v_escape_boxed_744_; lean_object* v_res_745_; 
v_escape_boxed_744_ = lean_unbox(v_escape_743_);
v_res_745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_742_, v_escape_boxed_744_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_746_, uint8_t v_escape_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_746_, v_escape_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_749_, lean_object* v_escape_750_){
_start:
{
uint8_t v_escape_boxed_751_; lean_object* v_res_752_; 
v_escape_boxed_751_ = lean_unbox(v_escape_750_);
v_res_752_ = l_Lean_Name_toString(v_n_749_, v_escape_boxed_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_753_){
_start:
{
uint8_t v___x_754_; lean_object* v___x_755_; 
v___x_754_ = 1;
v___x_755_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_753_, v___x_754_);
return v___x_755_;
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
