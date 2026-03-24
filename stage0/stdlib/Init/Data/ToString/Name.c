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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object*, lean_object*);
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
lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; uint8_t v___y_151_; uint32_t v___y_153_; uint8_t v___y_154_; uint32_t v___y_159_; uint32_t v___y_165_; uint8_t v___y_171_; lean_object* v___x_182_; uint8_t v_c_183_; uint8_t v___y_185_; uint8_t v___y_189_; uint8_t v___x_194_; uint8_t v___x_195_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v_c_183_ = lean_string_get_byte_fast(v_s_121_, v___x_182_);
v___x_194_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_195_ = lean_uint8_dec_le(v___x_194_, v_c_183_);
if (v___x_195_ == 0)
{
v___y_189_ = v___x_195_;
goto v___jp_188_;
}
else
{
uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_197_ = lean_uint8_dec_le(v_c_183_, v___x_196_);
v___y_189_ = v___x_197_;
goto v___jp_188_;
}
v___jp_122_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v_startInclusive_128_; lean_object* v_endExclusive_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
lean_inc_ref(v___y_123_);
v___x_126_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_123_);
lean_inc(v___y_124_);
v___x_127_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___y_125_, v___y_123_, v___x_126_, v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec_ref(v___y_125_);
v_startInclusive_128_ = lean_ctor_get(v___x_127_, 1);
lean_inc(v_startInclusive_128_);
v_endExclusive_129_ = lean_ctor_get(v___x_127_, 2);
lean_inc(v_endExclusive_129_);
lean_dec_ref(v___x_127_);
v___x_130_ = lean_nat_sub(v_endExclusive_129_, v_startInclusive_128_);
lean_dec(v_startInclusive_128_);
lean_dec(v_endExclusive_129_);
v___x_131_ = lean_nat_dec_eq(v___x_130_, v___y_124_);
lean_dec(v___y_124_);
lean_dec(v___x_130_);
return v___x_131_;
}
v___jp_132_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_137_ = l_panic___redArg(v___y_135_, v___x_136_);
v___y_123_ = v___y_133_;
v___y_124_ = v___y_134_;
v___y_125_ = v___x_137_;
goto v___jp_122_;
}
v___jp_138_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_141_, 0, v_s_121_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = l_Substring_Raw_nextn(v___x_141_, v___x_142_, v___x_139_);
lean_dec_ref(v___x_141_);
v___x_144_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_145_ = l_String_instInhabitedSlice;
v___x_146_ = lean_string_is_valid_pos(v_s_121_, v___x_143_);
if (v___x_146_ == 0)
{
lean_dec(v___x_143_);
lean_dec_ref(v_s_121_);
v___y_133_ = v___x_144_;
v___y_134_ = v___x_139_;
v___y_135_ = v___x_145_;
goto v___jp_132_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = lean_string_is_valid_pos(v_s_121_, v___x_140_);
if (v___x_147_ == 0)
{
lean_dec(v___x_143_);
lean_dec_ref(v_s_121_);
v___y_133_ = v___x_144_;
v___y_134_ = v___x_139_;
v___y_135_ = v___x_145_;
goto v___jp_132_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_le(v___x_143_, v___x_140_);
if (v___x_148_ == 0)
{
lean_dec(v___x_143_);
lean_dec_ref(v_s_121_);
v___y_133_ = v___x_144_;
v___y_134_ = v___x_139_;
v___y_135_ = v___x_145_;
goto v___jp_132_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v_s_121_);
lean_ctor_set(v___x_149_, 1, v___x_143_);
lean_ctor_set(v___x_149_, 2, v___x_140_);
v___y_123_ = v___x_144_;
v___y_124_ = v___x_139_;
v___y_125_ = v___x_149_;
goto v___jp_122_;
}
}
}
}
v___jp_150_:
{
if (v___y_151_ == 0)
{
lean_dec_ref(v_s_121_);
return v___y_151_;
}
else
{
goto v___jp_138_;
}
}
v___jp_152_:
{
if (v___y_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 95;
v___x_156_ = lean_uint32_dec_eq(v___y_153_, v___x_155_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
v___x_157_ = l_Lean_isLetterLike(v___y_153_);
v___y_151_ = v___x_157_;
goto v___jp_150_;
}
else
{
v___y_151_ = v___x_156_;
goto v___jp_150_;
}
}
else
{
goto v___jp_138_;
}
}
v___jp_158_:
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 97;
v___x_161_ = lean_uint32_dec_le(v___x_160_, v___y_159_);
if (v___x_161_ == 0)
{
v___y_153_ = v___y_159_;
v___y_154_ = v___x_161_;
goto v___jp_152_;
}
else
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 122;
v___x_163_ = lean_uint32_dec_le(v___y_159_, v___x_162_);
v___y_153_ = v___y_159_;
v___y_154_ = v___x_163_;
goto v___jp_152_;
}
}
v___jp_164_:
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 65;
v___x_167_ = lean_uint32_dec_le(v___x_166_, v___y_165_);
if (v___x_167_ == 0)
{
v___y_159_ = v___y_165_;
goto v___jp_158_;
}
else
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 90;
v___x_169_ = lean_uint32_dec_le(v___y_165_, v___x_168_);
if (v___x_169_ == 0)
{
v___y_159_ = v___y_165_;
goto v___jp_158_;
}
else
{
goto v___jp_138_;
}
}
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_174_, 0, v_s_121_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
v___x_175_ = l_String_Slice_Pos_get_x3f(v___x_174_, v___x_172_);
lean_dec_ref(v___x_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint32_t v___x_176_; 
v___x_176_ = 65;
v___y_165_ = v___x_176_;
goto v___jp_164_;
}
else
{
lean_object* v_val_177_; uint32_t v___x_178_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v___x_175_);
v___x_178_ = lean_unbox_uint32(v_val_177_);
lean_dec(v_val_177_);
v___y_165_ = v___x_178_;
goto v___jp_164_;
}
}
else
{
lean_dec_ref(v_s_121_);
return v___y_171_;
}
}
v___jp_179_:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_121_, v___x_180_);
v___y_171_ = v___x_181_;
goto v___jp_170_;
}
v___jp_184_:
{
if (v___y_185_ == 0)
{
uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_187_ = lean_uint8_dec_eq(v_c_183_, v___x_186_);
if (v___x_187_ == 0)
{
v___y_171_ = v___x_187_;
goto v___jp_170_;
}
else
{
goto v___jp_179_;
}
}
else
{
goto v___jp_179_;
}
}
v___jp_188_:
{
if (v___y_189_ == 0)
{
uint8_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_191_ = lean_uint8_dec_le(v___x_190_, v_c_183_);
if (v___x_191_ == 0)
{
v___y_185_ = v___x_191_;
goto v___jp_184_;
}
else
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_193_ = lean_uint8_dec_le(v_c_183_, v___x_192_);
v___y_185_ = v___x_193_;
goto v___jp_184_;
}
}
else
{
goto v___jp_179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(lean_object* v_s_201_, lean_object* v_h_202_){
_start:
{
lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; uint8_t v___y_232_; uint32_t v___y_234_; uint8_t v___y_235_; uint32_t v___y_240_; uint32_t v___y_246_; uint8_t v___y_252_; lean_object* v___x_263_; uint8_t v_c_264_; uint8_t v___y_266_; uint8_t v___y_270_; uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v_c_264_ = lean_string_get_byte_fast(v_s_201_, v___x_263_);
v___x_275_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_276_ = lean_uint8_dec_le(v___x_275_, v_c_264_);
if (v___x_276_ == 0)
{
v___y_270_ = v___x_276_;
goto v___jp_269_;
}
else
{
uint8_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_278_ = lean_uint8_dec_le(v_c_264_, v___x_277_);
v___y_270_ = v___x_278_;
goto v___jp_269_;
}
v___jp_203_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_startInclusive_209_; lean_object* v_endExclusive_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
lean_inc_ref(v___y_204_);
v___x_207_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_204_);
lean_inc(v___y_205_);
v___x_208_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___y_206_, v___y_204_, v___x_207_, v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec_ref(v___y_206_);
v_startInclusive_209_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_startInclusive_209_);
v_endExclusive_210_ = lean_ctor_get(v___x_208_, 2);
lean_inc(v_endExclusive_210_);
lean_dec_ref(v___x_208_);
v___x_211_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
lean_dec(v_startInclusive_209_);
lean_dec(v_endExclusive_210_);
v___x_212_ = lean_nat_dec_eq(v___x_211_, v___y_205_);
lean_dec(v___y_205_);
lean_dec(v___x_211_);
return v___x_212_;
}
v___jp_213_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_218_ = l_panic___redArg(v___y_216_, v___x_217_);
v___y_204_ = v___y_214_;
v___y_205_ = v___y_215_;
v___y_206_ = v___x_218_;
goto v___jp_203_;
}
v___jp_219_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_string_utf8_byte_size(v_s_201_);
lean_inc_ref(v_s_201_);
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v_s_201_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = l_Substring_Raw_nextn(v___x_222_, v___x_223_, v___x_220_);
lean_dec_ref(v___x_222_);
v___x_225_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_226_ = l_String_instInhabitedSlice;
v___x_227_ = lean_string_is_valid_pos(v_s_201_, v___x_224_);
if (v___x_227_ == 0)
{
lean_dec(v___x_224_);
lean_dec_ref(v_s_201_);
v___y_214_ = v___x_225_;
v___y_215_ = v___x_220_;
v___y_216_ = v___x_226_;
goto v___jp_213_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = lean_string_is_valid_pos(v_s_201_, v___x_221_);
if (v___x_228_ == 0)
{
lean_dec(v___x_224_);
lean_dec_ref(v_s_201_);
v___y_214_ = v___x_225_;
v___y_215_ = v___x_220_;
v___y_216_ = v___x_226_;
goto v___jp_213_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_le(v___x_224_, v___x_221_);
if (v___x_229_ == 0)
{
lean_dec(v___x_224_);
lean_dec_ref(v_s_201_);
v___y_214_ = v___x_225_;
v___y_215_ = v___x_220_;
v___y_216_ = v___x_226_;
goto v___jp_213_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v_s_201_);
lean_ctor_set(v___x_230_, 1, v___x_224_);
lean_ctor_set(v___x_230_, 2, v___x_221_);
v___y_204_ = v___x_225_;
v___y_205_ = v___x_220_;
v___y_206_ = v___x_230_;
goto v___jp_203_;
}
}
}
}
v___jp_231_:
{
if (v___y_232_ == 0)
{
lean_dec_ref(v_s_201_);
return v___y_232_;
}
else
{
goto v___jp_219_;
}
}
v___jp_233_:
{
if (v___y_235_ == 0)
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 95;
v___x_237_ = lean_uint32_dec_eq(v___y_234_, v___x_236_);
if (v___x_237_ == 0)
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_isLetterLike(v___y_234_);
v___y_232_ = v___x_238_;
goto v___jp_231_;
}
else
{
v___y_232_ = v___x_237_;
goto v___jp_231_;
}
}
else
{
goto v___jp_219_;
}
}
v___jp_239_:
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 97;
v___x_242_ = lean_uint32_dec_le(v___x_241_, v___y_240_);
if (v___x_242_ == 0)
{
v___y_234_ = v___y_240_;
v___y_235_ = v___x_242_;
goto v___jp_233_;
}
else
{
uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = 122;
v___x_244_ = lean_uint32_dec_le(v___y_240_, v___x_243_);
v___y_234_ = v___y_240_;
v___y_235_ = v___x_244_;
goto v___jp_233_;
}
}
v___jp_245_:
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 65;
v___x_248_ = lean_uint32_dec_le(v___x_247_, v___y_246_);
if (v___x_248_ == 0)
{
v___y_240_ = v___y_246_;
goto v___jp_239_;
}
else
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 90;
v___x_250_ = lean_uint32_dec_le(v___y_246_, v___x_249_);
if (v___x_250_ == 0)
{
v___y_240_ = v___y_246_;
goto v___jp_239_;
}
else
{
goto v___jp_219_;
}
}
}
v___jp_251_:
{
if (v___y_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_string_utf8_byte_size(v_s_201_);
lean_inc_ref(v_s_201_);
v___x_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_255_, 0, v_s_201_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
v___x_256_ = l_String_Slice_Pos_get_x3f(v___x_255_, v___x_253_);
lean_dec_ref(v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
uint32_t v___x_257_; 
v___x_257_ = 65;
v___y_246_ = v___x_257_;
goto v___jp_245_;
}
else
{
lean_object* v_val_258_; uint32_t v___x_259_; 
v_val_258_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_val_258_);
lean_dec_ref(v___x_256_);
v___x_259_ = lean_unbox_uint32(v_val_258_);
lean_dec(v_val_258_);
v___y_246_ = v___x_259_;
goto v___jp_245_;
}
}
else
{
lean_dec_ref(v_s_201_);
return v___y_252_;
}
}
v___jp_260_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_201_, v___x_261_);
v___y_252_ = v___x_262_;
goto v___jp_251_;
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_268_ = lean_uint8_dec_eq(v_c_264_, v___x_267_);
if (v___x_268_ == 0)
{
v___y_252_ = v___x_268_;
goto v___jp_251_;
}
else
{
goto v___jp_260_;
}
}
else
{
goto v___jp_260_;
}
}
v___jp_269_:
{
if (v___y_270_ == 0)
{
uint8_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_272_ = lean_uint8_dec_le(v___x_271_, v_c_264_);
if (v___x_272_ == 0)
{
v___y_266_ = v___x_272_;
goto v___jp_265_;
}
else
{
uint8_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_274_ = lean_uint8_dec_le(v_c_264_, v___x_273_);
v___y_266_ = v___x_274_;
goto v___jp_265_;
}
}
else
{
goto v___jp_260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_279_, lean_object* v_h_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_279_, v_h_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = l_Lean_idBeginEscape;
v___x_285_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_286_ = lean_string_push(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2(void){
_start:
{
uint32_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_idEndEscape;
v___x_288_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0));
v___x_289_ = lean_string_push(v___x_288_, v___x_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape(lean_object* v_s_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_292_ = lean_string_append(v___x_291_, v_s_290_);
v___x_293_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(lean_object* v_s_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_295_);
lean_dec_ref(v_s_295_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_Name_escapePart___lam__0___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Name_escapePart___lam__0___closed__0));
v___x_299_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___lam__0(lean_object* v_s_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_Name_escapePart___lam__0___closed__1, &l_Lean_Name_escapePart___lam__0___closed__1_once, _init_l_Lean_Name_escapePart___lam__0___closed__1);
v___x_308_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_300_, v___x_307_, v___y_301_, lean_box(0), lean_box(0), v___y_304_, v___y_305_, v___y_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart(lean_object* v_s_312_, uint8_t v_force_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_string_utf8_byte_size(v_s_312_);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_318_ = lean_string_append(v___x_317_, v_s_312_);
lean_dec_ref(v_s_312_);
v___x_319_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___f_322_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; uint8_t v___y_361_; uint32_t v___y_363_; uint8_t v___y_364_; uint32_t v___y_369_; uint32_t v___y_375_; uint8_t v___y_381_; 
v___f_322_ = ((lean_object*)(l_Lean_Name_escapePart___closed__0));
if (v_force_313_ == 0)
{
uint8_t v_c_391_; uint8_t v___y_393_; uint8_t v___y_397_; uint8_t v___x_402_; uint8_t v___x_403_; 
v_c_391_ = lean_string_get_byte_fast(v_s_312_, v___x_314_);
v___x_402_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_403_ = lean_uint8_dec_le(v___x_402_, v_c_391_);
if (v___x_403_ == 0)
{
v___y_397_ = v___x_403_;
goto v___jp_396_;
}
else
{
uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_405_ = lean_uint8_dec_le(v_c_391_, v___x_404_);
v___y_397_ = v___x_405_;
goto v___jp_396_;
}
v___jp_392_:
{
if (v___y_393_ == 0)
{
uint8_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_395_ = lean_uint8_dec_eq(v_c_391_, v___x_394_);
if (v___x_395_ == 0)
{
v___y_381_ = v___x_395_;
goto v___jp_380_;
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
v___jp_396_:
{
if (v___y_397_ == 0)
{
uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_399_ = lean_uint8_dec_le(v___x_398_, v_c_391_);
if (v___x_399_ == 0)
{
v___y_393_ = v___x_399_;
goto v___jp_392_;
}
else
{
uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_401_ = lean_uint8_dec_le(v_c_391_, v___x_400_);
v___y_393_ = v___x_401_;
goto v___jp_392_;
}
}
else
{
goto v___jp_388_;
}
}
}
else
{
goto v___jp_323_;
}
v___jp_323_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = ((lean_object*)(l_Lean_Name_escapePart___closed__1));
lean_inc_ref(v_s_312_);
v___x_325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_325_, 0, v_s_312_);
lean_ctor_set(v___x_325_, 1, v___x_314_);
lean_ctor_set(v___x_325_, 2, v___x_315_);
v___x_326_ = l_String_Slice_contains___redArg(v___f_322_, v___x_325_, v___x_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_328_ = lean_string_append(v___x_327_, v_s_312_);
lean_dec_ref(v_s_312_);
v___x_329_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_330_ = lean_string_append(v___x_328_, v___x_329_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; 
lean_dec_ref(v_s_312_);
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
v___jp_333_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_startInclusive_339_; lean_object* v_endExclusive_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
lean_inc_ref(v___y_334_);
v___x_337_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_334_);
lean_inc(v___y_335_);
v___x_338_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___y_336_, v___y_334_, v___x_337_, v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec_ref(v___y_336_);
v_startInclusive_339_ = lean_ctor_get(v___x_338_, 1);
lean_inc(v_startInclusive_339_);
v_endExclusive_340_ = lean_ctor_get(v___x_338_, 2);
lean_inc(v_endExclusive_340_);
lean_dec_ref(v___x_338_);
v___x_341_ = lean_nat_sub(v_endExclusive_340_, v_startInclusive_339_);
lean_dec(v_startInclusive_339_);
lean_dec(v_endExclusive_340_);
v___x_342_ = lean_nat_dec_eq(v___x_341_, v___y_335_);
lean_dec(v___y_335_);
lean_dec(v___x_341_);
if (v___x_342_ == 0)
{
goto v___jp_323_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_s_312_);
return v___x_343_;
}
}
v___jp_344_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_349_ = l_panic___redArg(v___y_346_, v___x_348_);
v___y_334_ = v___y_345_;
v___y_335_ = v___y_347_;
v___y_336_ = v___x_349_;
goto v___jp_333_;
}
v___jp_350_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
lean_inc_ref(v_s_312_);
v___x_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_351_, 0, v_s_312_);
lean_ctor_set(v___x_351_, 1, v___x_314_);
lean_ctor_set(v___x_351_, 2, v___x_315_);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = l_Substring_Raw_nextn(v___x_351_, v___x_352_, v___x_314_);
lean_dec_ref(v___x_351_);
v___x_354_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4));
v___x_355_ = l_String_instInhabitedSlice;
v___x_356_ = lean_string_is_valid_pos(v_s_312_, v___x_353_);
if (v___x_356_ == 0)
{
lean_dec(v___x_353_);
v___y_345_ = v___x_354_;
v___y_346_ = v___x_355_;
v___y_347_ = v___x_314_;
goto v___jp_344_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = lean_string_is_valid_pos(v_s_312_, v___x_315_);
if (v___x_357_ == 0)
{
lean_dec(v___x_353_);
v___y_345_ = v___x_354_;
v___y_346_ = v___x_355_;
v___y_347_ = v___x_314_;
goto v___jp_344_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_le(v___x_353_, v___x_315_);
if (v___x_358_ == 0)
{
lean_dec(v___x_353_);
v___y_345_ = v___x_354_;
v___y_346_ = v___x_355_;
v___y_347_ = v___x_314_;
goto v___jp_344_;
}
else
{
lean_object* v___x_359_; 
lean_inc_ref(v_s_312_);
v___x_359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_359_, 0, v_s_312_);
lean_ctor_set(v___x_359_, 1, v___x_353_);
lean_ctor_set(v___x_359_, 2, v___x_315_);
v___y_334_ = v___x_354_;
v___y_335_ = v___x_314_;
v___y_336_ = v___x_359_;
goto v___jp_333_;
}
}
}
}
v___jp_360_:
{
if (v___y_361_ == 0)
{
goto v___jp_323_;
}
else
{
goto v___jp_350_;
}
}
v___jp_362_:
{
if (v___y_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 95;
v___x_366_ = lean_uint32_dec_eq(v___y_363_, v___x_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = l_Lean_isLetterLike(v___y_363_);
v___y_361_ = v___x_367_;
goto v___jp_360_;
}
else
{
v___y_361_ = v___x_366_;
goto v___jp_360_;
}
}
else
{
goto v___jp_350_;
}
}
v___jp_368_:
{
uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 97;
v___x_371_ = lean_uint32_dec_le(v___x_370_, v___y_369_);
if (v___x_371_ == 0)
{
v___y_363_ = v___y_369_;
v___y_364_ = v___x_371_;
goto v___jp_362_;
}
else
{
uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = 122;
v___x_373_ = lean_uint32_dec_le(v___y_369_, v___x_372_);
v___y_363_ = v___y_369_;
v___y_364_ = v___x_373_;
goto v___jp_362_;
}
}
v___jp_374_:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 65;
v___x_377_ = lean_uint32_dec_le(v___x_376_, v___y_375_);
if (v___x_377_ == 0)
{
v___y_369_ = v___y_375_;
goto v___jp_368_;
}
else
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 90;
v___x_379_ = lean_uint32_dec_le(v___y_375_, v___x_378_);
if (v___x_379_ == 0)
{
v___y_369_ = v___y_375_;
goto v___jp_368_;
}
else
{
goto v___jp_350_;
}
}
}
v___jp_380_:
{
if (v___y_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc_ref(v_s_312_);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v_s_312_);
lean_ctor_set(v___x_382_, 1, v___x_314_);
lean_ctor_set(v___x_382_, 2, v___x_315_);
v___x_383_ = l_String_Slice_Pos_get_x3f(v___x_382_, v___x_314_);
lean_dec_ref(v___x_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
uint32_t v___x_384_; 
v___x_384_ = 65;
v___y_375_ = v___x_384_;
goto v___jp_374_;
}
else
{
lean_object* v_val_385_; uint32_t v___x_386_; 
v_val_385_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_val_385_);
lean_dec_ref(v___x_383_);
v___x_386_ = lean_unbox_uint32(v_val_385_);
lean_dec(v_val_385_);
v___y_375_ = v___x_386_;
goto v___jp_374_;
}
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v_s_312_);
return v___x_387_;
}
}
v___jp_388_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_312_, v___x_389_);
v___y_381_ = v___x_390_;
goto v___jp_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_escapePart___boxed(lean_object* v_s_406_, lean_object* v_force_407_){
_start:
{
uint8_t v_force_boxed_408_; lean_object* v_res_409_; 
v_force_boxed_408_ = lean_unbox(v_force_407_);
v_res_409_ = l_Lean_Name_escapePart(v_s_406_, v_force_boxed_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(lean_object* v_msg_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l_String_instInhabitedSlice;
v___x_412_ = lean_panic_fn(v___x_411_, v_msg_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(lean_object* v_s_413_, lean_object* v_curr_414_){
_start:
{
lean_object* v_str_415_; lean_object* v_startInclusive_416_; lean_object* v_endExclusive_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___y_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_str_415_ = lean_ctor_get(v_s_413_, 0);
v_startInclusive_416_ = lean_ctor_get(v_s_413_, 1);
v_endExclusive_417_ = lean_ctor_get(v_s_413_, 2);
v___x_418_ = lean_nat_add(v_startInclusive_416_, v_curr_414_);
lean_inc(v_endExclusive_417_);
lean_inc(v___x_418_);
lean_inc_ref(v_str_415_);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_str_415_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
lean_ctor_set(v___x_419_, 2, v_endExclusive_417_);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_nat_sub(v_endExclusive_417_, v___x_418_);
v___x_430_ = lean_nat_dec_eq(v___x_428_, v___x_429_);
lean_dec(v___x_429_);
if (v___x_430_ == 0)
{
uint32_t v___x_431_; uint8_t v___y_433_; uint8_t v___y_445_; uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_431_ = lean_string_utf8_get_fast(v_str_415_, v___x_418_);
v___x_455_ = 65;
v___x_456_ = lean_uint32_dec_le(v___x_455_, v___x_431_);
if (v___x_456_ == 0)
{
goto v___jp_450_;
}
else
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 90;
v___x_458_ = lean_uint32_dec_le(v___x_431_, v___x_457_);
if (v___x_458_ == 0)
{
goto v___jp_450_;
}
else
{
goto v___jp_420_;
}
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 95;
v___x_435_ = lean_uint32_dec_eq(v___x_431_, v___x_434_);
if (v___x_435_ == 0)
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 39;
v___x_437_ = lean_uint32_dec_eq(v___x_431_, v___x_436_);
if (v___x_437_ == 0)
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 33;
v___x_439_ = lean_uint32_dec_eq(v___x_431_, v___x_438_);
if (v___x_439_ == 0)
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 63;
v___x_441_ = lean_uint32_dec_eq(v___x_431_, v___x_440_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_isLetterLike(v___x_431_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_isSubScriptAlnum(v___x_431_);
v___y_427_ = v___x_443_;
goto v___jp_426_;
}
else
{
v___y_427_ = v___x_442_;
goto v___jp_426_;
}
}
else
{
v___y_427_ = v___x_441_;
goto v___jp_426_;
}
}
else
{
v___y_427_ = v___x_439_;
goto v___jp_426_;
}
}
else
{
v___y_427_ = v___x_437_;
goto v___jp_426_;
}
}
else
{
v___y_427_ = v___x_435_;
goto v___jp_426_;
}
}
else
{
goto v___jp_420_;
}
}
v___jp_444_:
{
if (v___y_445_ == 0)
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 48;
v___x_447_ = lean_uint32_dec_le(v___x_446_, v___x_431_);
if (v___x_447_ == 0)
{
v___y_433_ = v___x_447_;
goto v___jp_432_;
}
else
{
uint32_t v___x_448_; uint8_t v___x_449_; 
v___x_448_ = 57;
v___x_449_ = lean_uint32_dec_le(v___x_431_, v___x_448_);
v___y_433_ = v___x_449_;
goto v___jp_432_;
}
}
else
{
goto v___jp_420_;
}
}
v___jp_450_:
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 97;
v___x_452_ = lean_uint32_dec_le(v___x_451_, v___x_431_);
if (v___x_452_ == 0)
{
v___y_445_ = v___x_452_;
goto v___jp_444_;
}
else
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 122;
v___x_454_ = lean_uint32_dec_le(v___x_431_, v___x_453_);
v___y_445_ = v___x_454_;
goto v___jp_444_;
}
}
}
else
{
lean_dec(v___x_418_);
lean_dec(v_curr_414_);
return v___x_419_;
}
v___jp_420_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_string_utf8_next_fast(v_str_415_, v___x_418_);
v___x_422_ = lean_nat_sub(v___x_421_, v___x_418_);
lean_dec(v___x_418_);
v___x_423_ = lean_nat_add(v_curr_414_, v___x_422_);
lean_dec(v___x_422_);
v___x_424_ = lean_nat_dec_lt(v_curr_414_, v___x_423_);
lean_dec(v_curr_414_);
if (v___x_424_ == 0)
{
lean_dec(v___x_423_);
return v___x_419_;
}
else
{
lean_dec_ref(v___x_419_);
v_curr_414_ = v___x_423_;
goto _start;
}
}
v___jp_426_:
{
if (v___y_427_ == 0)
{
lean_dec(v___x_418_);
lean_dec(v_curr_414_);
return v___x_419_;
}
else
{
goto v___jp_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(lean_object* v_s_459_, lean_object* v_curr_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_459_, v_curr_460_);
lean_dec_ref(v_s_459_);
return v_res_461_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(lean_object* v_s_462_, lean_object* v_a_463_, uint8_t v_b_464_){
_start:
{
lean_object* v_str_465_; lean_object* v_startInclusive_466_; lean_object* v_endExclusive_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_str_465_ = lean_ctor_get(v_s_462_, 0);
v_startInclusive_466_ = lean_ctor_get(v_s_462_, 1);
v_endExclusive_467_ = lean_ctor_get(v_s_462_, 2);
v___x_468_ = lean_nat_sub(v_endExclusive_467_, v_startInclusive_466_);
v___x_469_ = lean_nat_dec_eq(v_a_463_, v___x_468_);
lean_dec(v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint32_t v___x_471_; uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_nat_add(v_startInclusive_466_, v_a_463_);
lean_dec(v_a_463_);
v___x_471_ = lean_string_utf8_get_fast(v_str_465_, v___x_470_);
v___x_472_ = 187;
v___x_473_ = lean_uint32_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_string_utf8_next_fast(v_str_465_, v___x_470_);
lean_dec(v___x_470_);
v___x_475_ = lean_nat_sub(v___x_474_, v_startInclusive_466_);
v_a_463_ = v___x_475_;
v_b_464_ = v___x_473_;
goto _start;
}
else
{
lean_dec(v___x_470_);
return v___x_473_;
}
}
else
{
lean_dec(v_a_463_);
return v_b_464_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(lean_object* v_s_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
uint8_t v_b_boxed_480_; uint8_t v_res_481_; lean_object* v_r_482_; 
v_b_boxed_480_ = lean_unbox(v_b_479_);
v_res_481_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_477_, v_a_478_, v_b_boxed_480_);
lean_dec_ref(v_s_477_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(lean_object* v_s_483_){
_start:
{
lean_object* v_searcher_484_; uint8_t v___x_485_; uint8_t v___x_486_; 
v_searcher_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = 0;
v___x_486_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_483_, v_searcher_484_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(lean_object* v_s_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_487_);
lean_dec_ref(v_s_487_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(uint8_t v_escape_490_, lean_object* v_s_491_, uint8_t v_force_492_){
_start:
{
lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_511_; uint8_t v___y_525_; uint32_t v___y_527_; uint8_t v___y_528_; uint32_t v___y_533_; uint32_t v___y_539_; uint8_t v___y_545_; 
if (v_escape_490_ == 0)
{
return v_s_491_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_string_utf8_byte_size(v_s_491_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_560_ = lean_string_append(v___x_559_, v_s_491_);
lean_dec_ref(v_s_491_);
v___x_561_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
return v___x_562_;
}
else
{
if (v_force_492_ == 0)
{
uint8_t v_c_563_; uint8_t v___y_565_; uint8_t v___y_569_; uint8_t v___x_574_; uint8_t v___x_575_; 
v_c_563_ = lean_string_get_byte_fast(v_s_491_, v___x_556_);
v___x_574_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
v___x_575_ = lean_uint8_dec_le(v___x_574_, v_c_563_);
if (v___x_575_ == 0)
{
v___y_569_ = v___x_575_;
goto v___jp_568_;
}
else
{
uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
v___x_577_ = lean_uint8_dec_le(v_c_563_, v___x_576_);
v___y_569_ = v___x_577_;
goto v___jp_568_;
}
v___jp_564_:
{
if (v___y_565_ == 0)
{
uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
v___x_567_ = lean_uint8_dec_eq(v_c_563_, v___x_566_);
if (v___x_567_ == 0)
{
v___y_545_ = v___x_567_;
goto v___jp_544_;
}
else
{
goto v___jp_553_;
}
}
else
{
goto v___jp_553_;
}
}
v___jp_568_:
{
if (v___y_569_ == 0)
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
v___x_571_ = lean_uint8_dec_le(v___x_570_, v_c_563_);
if (v___x_571_ == 0)
{
v___y_565_ = v___x_571_;
goto v___jp_564_;
}
else
{
uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_uint8_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
v___x_573_ = lean_uint8_dec_le(v_c_563_, v___x_572_);
v___y_565_ = v___x_573_;
goto v___jp_564_;
}
}
else
{
goto v___jp_553_;
}
}
}
else
{
goto v___jp_493_;
}
}
}
v___jp_493_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_string_utf8_byte_size(v_s_491_);
lean_inc_ref(v_s_491_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v_s_491_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v___x_497_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_496_);
lean_dec_ref(v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
v___x_499_ = lean_string_append(v___x_498_, v_s_491_);
lean_dec_ref(v_s_491_);
v___x_500_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2, &l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
return v___x_501_;
}
else
{
return v_s_491_;
}
}
v___jp_502_:
{
lean_object* v___x_505_; lean_object* v_startInclusive_506_; lean_object* v_endExclusive_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
lean_inc(v___y_503_);
v___x_505_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_504_, v___y_503_);
lean_dec_ref(v___y_504_);
v_startInclusive_506_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_startInclusive_506_);
v_endExclusive_507_ = lean_ctor_get(v___x_505_, 2);
lean_inc(v_endExclusive_507_);
lean_dec_ref(v___x_505_);
v___x_508_ = lean_nat_sub(v_endExclusive_507_, v_startInclusive_506_);
lean_dec(v_startInclusive_506_);
lean_dec(v_endExclusive_507_);
v___x_509_ = lean_nat_dec_eq(v___x_508_, v___y_503_);
lean_dec(v___y_503_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
goto v___jp_493_;
}
else
{
return v_s_491_;
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
v___x_513_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_512_);
v___y_503_ = v___y_511_;
v___y_504_ = v___x_513_;
goto v___jp_502_;
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_string_utf8_byte_size(v_s_491_);
lean_inc_ref(v_s_491_);
v___x_517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_517_, 0, v_s_491_);
lean_ctor_set(v___x_517_, 1, v___x_515_);
lean_ctor_set(v___x_517_, 2, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = l_Substring_Raw_nextn(v___x_517_, v___x_518_, v___x_515_);
lean_dec_ref(v___x_517_);
v___x_520_ = lean_string_is_valid_pos(v_s_491_, v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v___x_519_);
v___y_511_ = v___x_515_;
goto v___jp_510_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = lean_string_is_valid_pos(v_s_491_, v___x_516_);
if (v___x_521_ == 0)
{
lean_dec(v___x_519_);
v___y_511_ = v___x_515_;
goto v___jp_510_;
}
else
{
uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_le(v___x_519_, v___x_516_);
if (v___x_522_ == 0)
{
lean_dec(v___x_519_);
v___y_511_ = v___x_515_;
goto v___jp_510_;
}
else
{
lean_object* v___x_523_; 
lean_inc_ref(v_s_491_);
v___x_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_523_, 0, v_s_491_);
lean_ctor_set(v___x_523_, 1, v___x_519_);
lean_ctor_set(v___x_523_, 2, v___x_516_);
v___y_503_ = v___x_515_;
v___y_504_ = v___x_523_;
goto v___jp_502_;
}
}
}
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
goto v___jp_493_;
}
else
{
goto v___jp_514_;
}
}
v___jp_526_:
{
if (v___y_528_ == 0)
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 95;
v___x_530_ = lean_uint32_dec_eq(v___y_527_, v___x_529_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_isLetterLike(v___y_527_);
v___y_525_ = v___x_531_;
goto v___jp_524_;
}
else
{
v___y_525_ = v___x_530_;
goto v___jp_524_;
}
}
else
{
goto v___jp_514_;
}
}
v___jp_532_:
{
uint32_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = 97;
v___x_535_ = lean_uint32_dec_le(v___x_534_, v___y_533_);
if (v___x_535_ == 0)
{
v___y_527_ = v___y_533_;
v___y_528_ = v___x_535_;
goto v___jp_526_;
}
else
{
uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 122;
v___x_537_ = lean_uint32_dec_le(v___y_533_, v___x_536_);
v___y_527_ = v___y_533_;
v___y_528_ = v___x_537_;
goto v___jp_526_;
}
}
v___jp_538_:
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 65;
v___x_541_ = lean_uint32_dec_le(v___x_540_, v___y_539_);
if (v___x_541_ == 0)
{
v___y_533_ = v___y_539_;
goto v___jp_532_;
}
else
{
uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 90;
v___x_543_ = lean_uint32_dec_le(v___y_539_, v___x_542_);
if (v___x_543_ == 0)
{
v___y_533_ = v___y_539_;
goto v___jp_532_;
}
else
{
goto v___jp_514_;
}
}
}
v___jp_544_:
{
if (v___y_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_string_utf8_byte_size(v_s_491_);
lean_inc_ref(v_s_491_);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v_s_491_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
v___x_549_ = l_String_Slice_Pos_get_x3f(v___x_548_, v___x_546_);
lean_dec_ref(v___x_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
uint32_t v___x_550_; 
v___x_550_ = 65;
v___y_539_ = v___x_550_;
goto v___jp_538_;
}
else
{
lean_object* v_val_551_; uint32_t v___x_552_; 
v_val_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_551_);
lean_dec_ref(v___x_549_);
v___x_552_ = lean_unbox_uint32(v_val_551_);
lean_dec(v_val_551_);
v___y_539_ = v___x_552_;
goto v___jp_538_;
}
}
else
{
return v_s_491_;
}
}
v___jp_553_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_491_, v___x_554_);
v___y_545_ = v___x_555_;
goto v___jp_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_578_, lean_object* v_s_579_, lean_object* v_force_580_){
_start:
{
uint8_t v_escape_boxed_581_; uint8_t v_force_boxed_582_; lean_object* v_res_583_; 
v_escape_boxed_581_ = lean_unbox(v_escape_578_);
v_force_boxed_582_ = lean_unbox(v_force_580_);
v_res_583_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_boxed_581_, v_s_579_, v_force_boxed_582_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(lean_object* v_s_584_, lean_object* v_inst_585_, lean_object* v_R_586_, lean_object* v_a_587_, uint8_t v_b_588_, lean_object* v_c_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_584_, v_a_587_, v_b_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(lean_object* v_s_591_, lean_object* v_inst_592_, lean_object* v_R_593_, lean_object* v_a_594_, lean_object* v_b_595_, lean_object* v_c_596_){
_start:
{
uint8_t v_b_boxed_597_; uint8_t v_res_598_; lean_object* v_r_599_; 
v_b_boxed_597_ = lean_unbox(v_b_595_);
v_res_598_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_591_, v_inst_592_, v_R_593_, v_a_594_, v_b_boxed_597_, v_c_596_);
lean_dec_ref(v_s_591_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_toStringWithSep___lam__0(lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___lam__0___boxed(lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Lean_Name_toStringWithSep___lam__0(v_x_602_);
lean_dec_ref(v_x_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep(lean_object* v_sep_607_, uint8_t v_escape_608_, lean_object* v_n_609_, lean_object* v_isToken_610_){
_start:
{
switch(lean_obj_tag(v_n_609_))
{
case 0:
{
lean_object* v___x_611_; 
lean_dec_ref(v_isToken_610_);
v___x_611_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_611_;
}
case 1:
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_n_609_, 0);
if (lean_obj_tag(v_pre_612_) == 0)
{
lean_object* v_str_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; 
v_str_613_ = lean_ctor_get(v_n_609_, 1);
lean_inc_ref(v_str_613_);
lean_dec_ref(v_n_609_);
lean_inc_ref(v_str_613_);
v___x_614_ = lean_apply_1(v_isToken_610_, v_str_613_);
v___x_615_ = lean_unbox(v___x_614_);
v___x_616_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_608_, v_str_613_, v___x_615_);
return v___x_616_;
}
else
{
lean_object* v_str_617_; lean_object* v_r_618_; lean_object* v___x_619_; uint8_t v___x_620_; lean_object* v___x_621_; lean_object* v_r_x27_622_; 
lean_inc(v_pre_612_);
v_str_617_ = lean_ctor_get(v_n_609_, 1);
lean_inc_ref(v_str_617_);
lean_dec_ref(v_n_609_);
lean_inc_ref(v_isToken_610_);
v_r_618_ = l_Lean_Name_toStringWithSep(v_sep_607_, v_escape_608_, v_pre_612_, v_isToken_610_);
v___x_619_ = lean_string_append(v_r_618_, v_sep_607_);
v___x_620_ = 0;
lean_inc_ref(v_str_617_);
v___x_621_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_608_, v_str_617_, v___x_620_);
lean_inc_ref(v___x_619_);
v_r_x27_622_ = lean_string_append(v___x_619_, v___x_621_);
lean_dec_ref(v___x_621_);
if (v_escape_608_ == 0)
{
lean_dec_ref(v___x_619_);
lean_dec_ref(v_str_617_);
lean_dec_ref(v_isToken_610_);
return v_r_x27_622_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
lean_inc_ref(v_r_x27_622_);
v___x_623_ = lean_apply_1(v_isToken_610_, v_r_x27_622_);
v___x_624_ = lean_unbox(v___x_623_);
if (v___x_624_ == 0)
{
lean_dec_ref(v___x_619_);
lean_dec_ref(v_str_617_);
return v_r_x27_622_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec_ref(v_r_x27_622_);
v___x_625_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_608_, v_str_617_, v_escape_608_);
v___x_626_ = lean_string_append(v___x_619_, v___x_625_);
lean_dec_ref(v___x_625_);
return v___x_626_;
}
}
}
}
default: 
{
lean_object* v_pre_627_; 
lean_dec_ref(v_isToken_610_);
v_pre_627_ = lean_ctor_get(v_n_609_, 0);
if (lean_obj_tag(v_pre_627_) == 0)
{
lean_object* v_i_628_; lean_object* v___x_629_; 
v_i_628_ = lean_ctor_get(v_n_609_, 1);
lean_inc(v_i_628_);
lean_dec_ref(v_n_609_);
v___x_629_ = l_Nat_reprFast(v_i_628_);
return v___x_629_;
}
else
{
lean_object* v_i_630_; lean_object* v___f_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_inc(v_pre_627_);
v_i_630_ = lean_ctor_get(v_n_609_, 1);
lean_inc(v_i_630_);
lean_dec_ref(v_n_609_);
v___f_631_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__1));
v___x_632_ = l_Lean_Name_toStringWithSep(v_sep_607_, v_escape_608_, v_pre_627_, v___f_631_);
v___x_633_ = lean_string_append(v___x_632_, v_sep_607_);
v___x_634_ = l_Nat_reprFast(v_i_630_);
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
lean_dec_ref(v___x_634_);
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* v_sep_636_, lean_object* v_escape_637_, lean_object* v_n_638_, lean_object* v_isToken_639_){
_start:
{
uint8_t v_escape_boxed_640_; lean_object* v_res_641_; 
v_escape_boxed_640_ = lean_unbox(v_escape_637_);
v_res_641_ = l_Lean_Name_toStringWithSep(v_sep_636_, v_escape_boxed_640_, v_n_638_, v_isToken_639_);
lean_dec_ref(v_sep_636_);
return v_res_641_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_647_ = lean_string_utf8_byte_size(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_650_ = lean_string_utf8_byte_size(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(lean_object* v_n_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_653_ = lean_name_eq(v_n_651_, v___x_652_);
v___x_654_ = 1;
if (v___x_653_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Name_getRoot(v_n_651_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_str_656_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_str_656_ = lean_ctor_get(v___x_655_, 1);
lean_inc_ref(v_str_656_);
lean_dec_ref(v___x_655_);
v___x_664_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4));
v___x_665_ = lean_string_utf8_byte_size(v_str_656_);
v___x_666_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5);
v___x_667_ = lean_nat_dec_le(v___x_666_, v___x_665_);
if (v___x_667_ == 0)
{
goto v___jp_657_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_string_memcmp(v_str_656_, v___x_664_, v___x_668_, v___x_668_, v___x_666_);
if (v___x_669_ == 0)
{
goto v___jp_657_;
}
else
{
lean_dec_ref(v_str_656_);
return v___x_654_;
}
}
v___jp_657_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_658_ = ((lean_object*)(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_659_ = lean_string_utf8_byte_size(v_str_656_);
v___x_660_ = lean_obj_once(&l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3, &l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once, _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3);
v___x_661_ = lean_nat_dec_le(v___x_660_, v___x_659_);
if (v___x_661_ == 0)
{
lean_dec_ref(v_str_656_);
return v___x_653_;
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_string_memcmp(v_str_656_, v___x_658_, v___x_662_, v___x_662_, v___x_660_);
lean_dec_ref(v_str_656_);
return v___x_663_;
}
}
}
else
{
lean_dec(v___x_655_);
return v___x_653_;
}
}
else
{
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_670_);
lean_dec(v_n_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken(lean_object* v_n_674_, uint8_t v_escape_675_, lean_object* v_isToken_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_675_ == 0)
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Name_toStringWithSep(v___x_677_, v_escape_675_, v_n_674_, v_isToken_676_);
return v___x_678_;
}
else
{
uint8_t v___x_679_; 
lean_inc(v_n_674_);
v___x_679_ = lean_is_inaccessible_user_name(v_n_674_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = l_Lean_Name_hasMacroScopes(v_n_674_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; 
v___x_681_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_674_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Name_toStringWithSep(v___x_677_, v_escape_675_, v_n_674_, v_isToken_676_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Name_toStringWithSep(v___x_677_, v___x_680_, v_n_674_, v_isToken_676_);
return v___x_683_;
}
}
else
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Name_toStringWithSep(v___x_677_, v___x_679_, v_n_674_, v_isToken_676_);
return v___x_684_;
}
}
else
{
uint8_t v___x_685_; lean_object* v___x_686_; 
v___x_685_ = 0;
v___x_686_ = l_Lean_Name_toStringWithSep(v___x_677_, v___x_685_, v_n_674_, v_isToken_676_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___boxed(lean_object* v_n_687_, lean_object* v_escape_688_, lean_object* v_isToken_689_){
_start:
{
uint8_t v_escape_boxed_690_; lean_object* v_res_691_; 
v_escape_boxed_690_ = lean_unbox(v_escape_688_);
v_res_691_ = l_Lean_Name_toStringWithToken(v_n_687_, v_escape_boxed_690_, v_isToken_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(lean_object* v_sep_692_, uint8_t v_escape_693_, lean_object* v_n_694_){
_start:
{
switch(lean_obj_tag(v_n_694_))
{
case 0:
{
lean_object* v___x_695_; 
v___x_695_ = ((lean_object*)(l_Lean_Name_toStringWithSep___closed__0));
return v___x_695_;
}
case 1:
{
lean_object* v_pre_696_; 
v_pre_696_ = lean_ctor_get(v_n_694_, 0);
if (lean_obj_tag(v_pre_696_) == 0)
{
lean_object* v_str_697_; uint8_t v___x_698_; lean_object* v___x_699_; 
v_str_697_ = lean_ctor_get(v_n_694_, 1);
lean_inc_ref(v_str_697_);
lean_dec_ref(v_n_694_);
v___x_698_ = 0;
v___x_699_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_693_, v_str_697_, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v_str_700_; lean_object* v_r_701_; lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v_r_x27_705_; 
lean_inc(v_pre_696_);
v_str_700_ = lean_ctor_get(v_n_694_, 1);
lean_inc_ref(v_str_700_);
lean_dec_ref(v_n_694_);
v_r_701_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_692_, v_escape_693_, v_pre_696_);
v___x_702_ = lean_string_append(v_r_701_, v_sep_692_);
v___x_703_ = 0;
v___x_704_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_693_, v_str_700_, v___x_703_);
v_r_x27_705_ = lean_string_append(v___x_702_, v___x_704_);
lean_dec_ref(v___x_704_);
return v_r_x27_705_;
}
}
default: 
{
lean_object* v_pre_706_; 
v_pre_706_ = lean_ctor_get(v_n_694_, 0);
if (lean_obj_tag(v_pre_706_) == 0)
{
lean_object* v_i_707_; lean_object* v___x_708_; 
v_i_707_ = lean_ctor_get(v_n_694_, 1);
lean_inc(v_i_707_);
lean_dec_ref(v_n_694_);
v___x_708_ = l_Nat_reprFast(v_i_707_);
return v___x_708_;
}
else
{
lean_object* v_i_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_inc(v_pre_706_);
v_i_709_ = lean_ctor_get(v_n_694_, 1);
lean_inc(v_i_709_);
lean_dec_ref(v_n_694_);
v___x_710_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_692_, v_escape_693_, v_pre_706_);
v___x_711_ = lean_string_append(v___x_710_, v_sep_692_);
v___x_712_ = l_Nat_reprFast(v_i_709_);
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
lean_dec_ref(v___x_712_);
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(lean_object* v_sep_714_, lean_object* v_escape_715_, lean_object* v_n_716_){
_start:
{
uint8_t v_escape_boxed_717_; lean_object* v_res_718_; 
v_escape_boxed_717_ = lean_unbox(v_escape_715_);
v_res_718_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_714_, v_escape_boxed_717_, v_n_716_);
lean_dec_ref(v_sep_714_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object* v_n_719_, uint8_t v_escape_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = ((lean_object*)(l_Lean_Name_toStringWithToken___closed__0));
if (v_escape_720_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_721_, v_escape_720_, v_n_719_);
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
lean_inc(v_n_719_);
v___x_723_ = lean_is_inaccessible_user_name(v_n_719_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; 
v___x_724_ = l_Lean_Name_hasMacroScopes(v_n_719_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_719_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_721_, v_escape_720_, v_n_719_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_721_, v___x_724_, v_n_719_);
return v___x_727_;
}
}
else
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_721_, v___x_723_, v_n_719_);
return v___x_728_;
}
}
else
{
uint8_t v___x_729_; lean_object* v___x_730_; 
v___x_729_ = 0;
v___x_730_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_721_, v___x_729_, v_n_719_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(lean_object* v_n_731_, lean_object* v_escape_732_){
_start:
{
uint8_t v_escape_boxed_733_; lean_object* v_res_734_; 
v_escape_boxed_733_ = lean_unbox(v_escape_732_);
v_res_734_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_731_, v_escape_boxed_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString(lean_object* v_n_735_, uint8_t v_escape_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_735_, v_escape_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_toString___boxed(lean_object* v_n_738_, lean_object* v_escape_739_){
_start:
{
uint8_t v_escape_boxed_740_; lean_object* v_res_741_; 
v_escape_boxed_740_ = lean_unbox(v_escape_739_);
v_res_741_ = l_Lean_Name_toString(v_n_738_, v_escape_boxed_740_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instToString___lam__0(lean_object* v_n_742_){
_start:
{
uint8_t v___x_743_; lean_object* v___x_744_; 
v___x_743_ = 1;
v___x_744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_742_, v___x_743_);
return v___x_744_;
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
