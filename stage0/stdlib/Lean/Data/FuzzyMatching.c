// Lean compiler output
// Module: Lean.Data.FuzzyMatching
// Imports: public import Init.Data.Range.Polymorphic.Iterators public import Init.Data.Range.Polymorphic.Nat public import Init.Data.OfScientific public import Init.Data.Option.Coe public import Init.Data.Range import Init.Data.SInt.Basic import Init.Data.String.Basic import Lean.Server.Completion.CompletionUtils
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10;
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__11;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charType(uint32_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_instInhabitedCharRole_default;
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_instInhabitedCharRole;
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0;
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0;
uint16_t lean_int16_neg(uint16_t);
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful;
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object*);
lean_object* lean_int16_to_int(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Data.FuzzyMatching"};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0_value;
static const lean_string_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Data.FuzzyMatching.0.Lean.FuzzyMatching.Score.ofInt16!"};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1_value;
static const lean_string_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: x != awful.inner\n  "};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3;
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object*, lean_object*, lean_object*, lean_object*, uint16_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t, uint32_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0;
uint16_t lean_int16_add(uint16_t, uint16_t);
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern uint16_t l_instInhabitedInt16;
uint16_t lean_int16_sub(uint16_t, uint16_t);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint16_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0;
static double l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1;
static lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
static lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3;
uint8_t lean_float_decLe(double, double);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
double l_Float_ofInt(lean_object*);
double lean_float_div(double, double);
uint8_t l_String_charactersIn(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_nat_sub(x_5, x_1);
x_9 = lean_string_utf8_get(x_2, x_8);
lean_dec(x_8);
x_10 = lean_box_uint32(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_nat_sub(x_5, x_3);
x_13 = lean_string_utf8_get(x_2, x_12);
lean_dec(x_12);
x_14 = lean_string_utf8_get(x_2, x_5);
x_15 = lean_box_uint32(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box_uint32(x_13);
x_18 = lean_apply_3(x_4, x_11, x_17, x_16);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_mk_empty_array_with_capacity(x_6);
x_10 = lean_box(0);
x_11 = lean_string_utf8_get(x_2, x_4);
x_12 = lean_string_utf8_get(x_2, x_7);
x_13 = lean_box_uint32(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box_uint32(x_11);
lean_inc(x_1);
x_16 = lean_apply_3(x_1, x_10, x_15, x_14);
x_17 = lean_array_push(x_9, x_16);
x_18 = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9));
x_19 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed), 7, 4);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_7);
lean_closure_set(x_20, 3, x_1);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_7);
x_22 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), x_18, x_21, x_20, x_17, x_19, lean_box(0), lean_box(0));
x_23 = lean_nat_sub(x_6, x_19);
x_24 = lean_string_utf8_get(x_2, x_23);
lean_dec(x_23);
x_25 = lean_box_uint32(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_nat_sub(x_6, x_7);
x_28 = lean_string_utf8_get(x_2, x_27);
lean_dec(x_27);
lean_dec_ref(x_2);
x_29 = lean_box_uint32(x_28);
x_30 = lean_apply_3(x_1, x_26, x_29, x_10);
x_31 = lean_array_push(x_22, x_30);
return x_31;
}
else
{
lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_box(0);
x_33 = lean_string_utf8_get(x_2, x_4);
lean_dec_ref(x_2);
x_34 = lean_box_uint32(x_33);
x_35 = lean_apply_3(x_1, x_32, x_34, x_32);
x_36 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10;
x_37 = lean_array_push(x_36, x_35);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_38 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__11;
return x_38;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_2, x_4);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; uint32_t x_11; uint32_t x_17; uint32_t x_25; uint8_t x_26; 
x_7 = lean_string_utf8_get_fast(x_1, x_3);
x_8 = lean_string_utf8_get_fast(x_2, x_4);
x_9 = lean_string_utf8_next_fast(x_2, x_4);
lean_dec(x_4);
x_25 = 65;
x_26 = lean_uint32_dec_le(x_25, x_7);
if (x_26 == 0)
{
x_17 = x_7;
goto block_24;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 90;
x_28 = lean_uint32_dec_le(x_7, x_27);
if (x_28 == 0)
{
x_17 = x_7;
goto block_24;
}
else
{
uint32_t x_29; uint32_t x_30; 
x_29 = 32;
x_30 = lean_uint32_add(x_7, x_29);
x_17 = x_30;
goto block_24;
}
}
block_16:
{
uint8_t x_12; 
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_9;
goto _start;
}
}
block_24:
{
uint32_t x_18; uint8_t x_19; 
x_18 = 65;
x_19 = lean_uint32_dec_le(x_18, x_8);
if (x_19 == 0)
{
x_10 = x_17;
x_11 = x_8;
goto block_16;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 90;
x_21 = lean_uint32_dec_le(x_8, x_20);
if (x_21 == 0)
{
x_10 = x_17;
x_11 = x_8;
goto block_16;
}
else
{
uint32_t x_22; uint32_t x_23; 
x_22 = 32;
x_23 = lean_uint32_add(x_8, x_22);
x_10 = x_17;
x_11 = x_23;
goto block_16;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_FuzzyMatching_CharType_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharType_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_FuzzyMatching_CharType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharType_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_FuzzyMatching_CharType_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharType_lower_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_FuzzyMatching_CharType_lower_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharType_upper_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_FuzzyMatching_CharType_upper_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharType_separator_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_FuzzyMatching_CharType_separator_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charType(uint32_t x_1) {
_start:
{
uint8_t x_10; uint8_t x_13; uint32_t x_24; uint8_t x_25; 
x_24 = 65;
x_25 = lean_uint32_dec_le(x_24, x_1);
if (x_25 == 0)
{
goto block_23;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 90;
x_27 = lean_uint32_dec_le(x_1, x_26);
if (x_27 == 0)
{
goto block_23;
}
else
{
goto block_9;
}
}
block_9:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 65;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 90;
x_6 = lean_uint32_dec_le(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
block_12:
{
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 2;
return x_11;
}
else
{
goto block_9;
}
}
block_18:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 48;
x_15 = lean_uint32_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_10 = x_15;
goto block_12;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 57;
x_17 = lean_uint32_dec_le(x_1, x_16);
x_10 = x_17;
goto block_12;
}
}
else
{
goto block_9;
}
}
block_23:
{
uint32_t x_19; uint8_t x_20; 
x_19 = 97;
x_20 = lean_uint32_dec_le(x_19, x_1);
if (x_20 == 0)
{
x_13 = x_20;
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 122;
x_22 = lean_uint32_dec_le(x_1, x_21);
x_13 = x_22;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charType___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_FuzzyMatching_charType(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_FuzzyMatching_CharRole_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharRole_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_FuzzyMatching_CharRole_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_FuzzyMatching_CharRole_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_FuzzyMatching_CharRole_head_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_FuzzyMatching_CharRole_tail_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_FuzzyMatching_CharRole_separator_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 2)
{
uint8_t x_4; 
x_4 = 2;
return x_4;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unbox(x_6);
if (x_7 == 2)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
if (x_2 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_unbox(x_6);
if (x_10 == 1)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_FuzzyMatching_charRole(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_13 = lean_nat_dec_lt(x_4, x_5);
if (x_13 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_4, x_14);
x_16 = lean_string_utf8_get(x_1, x_15);
lean_dec(x_15);
x_17 = l_Lean_FuzzyMatching_charType(x_16);
if (x_17 == 2)
{
uint8_t x_18; 
x_18 = 2;
x_7 = x_18;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_sub(x_4, x_19);
x_21 = lean_string_utf8_get(x_1, x_20);
lean_dec(x_20);
x_22 = l_Lean_FuzzyMatching_charType(x_21);
if (x_22 == 2)
{
uint8_t x_23; 
x_23 = 0;
x_7 = x_23;
goto block_12;
}
else
{
if (x_17 == 0)
{
uint8_t x_24; 
x_24 = 1;
x_7 = x_24;
goto block_12;
}
else
{
if (x_22 == 1)
{
uint32_t x_25; uint8_t x_26; 
x_25 = lean_string_utf8_get(x_1, x_4);
x_26 = l_Lean_FuzzyMatching_charType(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = 0;
x_7 = x_27;
goto block_12;
}
else
{
uint8_t x_28; 
x_28 = 1;
x_7 = x_28;
goto block_12;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
x_7 = x_29;
goto block_12;
}
}
}
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_7);
x_9 = lean_array_push(x_3, x_8);
x_10 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_9;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_13 = lean_nat_dec_lt(x_4, x_5);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_4, x_14);
x_16 = lean_string_utf8_get(x_1, x_15);
lean_dec(x_15);
x_17 = l_Lean_FuzzyMatching_charType(x_16);
if (x_17 == 2)
{
uint8_t x_18; 
x_18 = 2;
x_7 = x_18;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_sub(x_4, x_19);
x_21 = lean_string_utf8_get(x_1, x_20);
lean_dec(x_20);
x_22 = l_Lean_FuzzyMatching_charType(x_21);
if (x_22 == 2)
{
uint8_t x_23; 
x_23 = 0;
x_7 = x_23;
goto block_12;
}
else
{
if (x_17 == 0)
{
uint8_t x_24; 
x_24 = 1;
x_7 = x_24;
goto block_12;
}
else
{
if (x_22 == 1)
{
uint32_t x_25; uint8_t x_26; 
x_25 = lean_string_utf8_get(x_1, x_4);
x_26 = l_Lean_FuzzyMatching_charType(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = 0;
x_7 = x_27;
goto block_12;
}
else
{
uint8_t x_28; 
x_28 = 1;
x_7 = x_28;
goto block_12;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
x_7 = x_29;
goto block_12;
}
}
}
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(x_7);
x_9 = lean_array_push(x_3, x_8);
x_10 = lean_nat_add(x_4, x_6);
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_21; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_21 = x_35;
goto block_34;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_unbox_uint32(x_37);
lean_dec(x_37);
x_39 = l_Lean_FuzzyMatching_charType(x_38);
x_40 = lean_box(x_39);
lean_ctor_set(x_1, 0, x_40);
x_21 = x_1;
goto block_34;
}
else
{
lean_object* x_41; uint32_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_43 = l_Lean_FuzzyMatching_charType(x_42);
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_21 = x_45;
goto block_34;
}
}
block_20:
{
if (x_5 == 2)
{
uint8_t x_7; 
lean_dec(x_6);
lean_dec(x_4);
x_7 = 2;
return x_7;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_unbox(x_9);
if (x_10 == 2)
{
uint8_t x_11; 
lean_dec(x_9);
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
if (x_5 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_6);
x_12 = 1;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_9);
lean_dec(x_9);
if (x_13 == 1)
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec_ref(x_6);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = 0;
return x_19;
}
}
}
}
}
}
block_34:
{
uint8_t x_22; 
x_22 = l_Lean_FuzzyMatching_charType(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_4 = x_21;
x_5 = x_22;
x_6 = x_23;
goto block_20;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_unbox_uint32(x_25);
lean_dec(x_25);
x_27 = l_Lean_FuzzyMatching_charType(x_26);
x_28 = lean_box(x_27);
lean_ctor_set(x_3, 0, x_28);
x_4 = x_21;
x_5 = x_22;
x_6 = x_3;
goto block_20;
}
else
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_31 = l_Lean_FuzzyMatching_charType(x_30);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_4 = x_21;
x_5 = x_22;
x_6 = x_33;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_length(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint32_t x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_mk_empty_array_with_capacity(x_5);
x_9 = lean_box(0);
x_10 = lean_string_utf8_get(x_1, x_3);
x_11 = lean_string_utf8_get(x_1, x_6);
x_12 = lean_box_uint32(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(x_9, x_10, x_13);
x_15 = lean_box(x_14);
x_16 = lean_array_push(x_8, x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_6);
x_19 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(x_1, x_18, x_16, x_17);
lean_dec_ref(x_18);
x_20 = lean_nat_sub(x_5, x_17);
x_21 = lean_string_utf8_get(x_1, x_20);
lean_dec(x_20);
x_22 = lean_box_uint32(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_nat_sub(x_5, x_6);
x_25 = lean_string_utf8_get(x_1, x_24);
lean_dec(x_24);
x_26 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(x_23, x_25, x_9);
x_27 = lean_box(x_26);
x_28 = lean_array_push(x_19, x_27);
return x_28;
}
else
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_box(0);
x_30 = lean_string_utf8_get(x_1, x_3);
x_31 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(x_29, x_30, x_29);
x_32 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0;
x_33 = lean_box(x_31);
x_34 = lean_array_push(x_32, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__1;
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default() {
_start:
{
uint16_t x_1; 
x_1 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0;
return x_1;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore() {
_start:
{
uint16_t x_1; 
x_1 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
return x_1;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(32768u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1() {
_start:
{
uint16_t x_1; uint16_t x_2; 
x_1 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0;
x_2 = lean_int16_neg(x_1);
return x_2;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful() {
_start:
{
uint16_t x_1; 
x_1 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_3 = lean_int16_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint8_t x_4; 
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_4 = lean_int16_dec_le(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint16_t x_7; 
x_5 = lean_box(x_1);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_3 = lean_int16_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_3 = lean_int16_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_int16_to_int(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(126u);
x_4 = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_3 = lean_int16_dec_eq(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
uint16_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint16_t x_8; 
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3;
x_6 = lean_box(x_4);
x_7 = l_panic___redArg(x_6, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int16_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_string_length(x_1);
x_5 = lean_nat_mul(x_2, x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_mul(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_mul(x_3, x_6);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_length(x_1);
x_5 = lean_nat_mul(x_2, x_4);
x_6 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint16_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint16_t x_14; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_6 = lean_string_length(x_1);
x_7 = lean_nat_mul(x_3, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mul(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_mul(x_4, x_8);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(x_5);
x_13 = lean_array_get_borrowed(x_12, x_2, x_11);
lean_dec(x_11);
x_14 = lean_unbox(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint16_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint16_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint16_t x_16; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_6 = lean_string_length(x_1);
x_7 = lean_nat_mul(x_3, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mul(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_mul(x_4, x_8);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_box(x_5);
x_15 = lean_array_get_borrowed(x_14, x_2, x_13);
lean_dec(x_13);
x_16 = lean_unbox(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint16_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint16_t x_5, uint16_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_string_length(x_1);
x_8 = lean_nat_mul(x_3, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_mul(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_mul(x_4, x_9);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(x_5);
x_14 = lean_array_set(x_2, x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_12, x_15);
lean_dec(x_12);
x_17 = lean_box(x_6);
x_18 = lean_array_set(x_14, x_16, x_17);
lean_dec(x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint16_t x_7; uint16_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = lean_unbox(x_6);
x_9 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
if (x_1 == 0)
{
uint16_t x_3; 
x_3 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
return x_3;
}
else
{
uint16_t x_4; 
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0;
return x_4;
}
}
else
{
uint16_t x_5; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t x_1, uint32_t x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
uint32_t x_5; uint32_t x_6; uint32_t x_10; uint32_t x_18; uint8_t x_19; 
x_18 = 65;
x_19 = lean_uint32_dec_le(x_18, x_1);
if (x_19 == 0)
{
x_10 = x_1;
goto block_17;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 90;
x_21 = lean_uint32_dec_le(x_1, x_20);
if (x_21 == 0)
{
x_10 = x_1;
goto block_17;
}
else
{
uint32_t x_22; uint32_t x_23; 
x_22 = 32;
x_23 = lean_uint32_add(x_1, x_22);
x_10 = x_23;
goto block_17;
}
}
block_9:
{
uint8_t x_7; 
x_7 = lean_uint32_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_7;
}
else
{
if (x_3 == 0)
{
if (x_4 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
else
{
return x_7;
}
}
}
block_17:
{
uint32_t x_11; uint8_t x_12; 
x_11 = 65;
x_12 = lean_uint32_dec_le(x_11, x_2);
if (x_12 == 0)
{
x_5 = x_10;
x_6 = x_2;
goto block_9;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 90;
x_14 = lean_uint32_dec_le(x_2, x_13);
if (x_14 == 0)
{
x_5 = x_10;
x_6 = x_2;
goto block_9;
}
else
{
uint32_t x_15; uint32_t x_16; 
x_15 = 32;
x_16 = lean_uint32_add(x_2, x_15);
x_5 = x_10;
x_6 = x_16;
goto block_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1() {
_start:
{
uint16_t x_1; uint16_t x_2; 
x_1 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
x_2 = lean_int16_add(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint16_t x_7) {
_start:
{
uint16_t x_8; uint16_t x_13; uint16_t x_19; uint8_t x_20; lean_object* x_24; uint16_t x_25; uint16_t x_33; uint8_t x_36; uint32_t x_38; uint32_t x_39; uint8_t x_40; 
x_24 = lean_unsigned_to_nat(1u);
x_33 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
x_38 = lean_string_utf8_get(x_1, x_3);
x_39 = lean_string_utf8_get(x_2, x_4);
x_40 = lean_uint32_dec_eq(x_38, x_39);
if (x_40 == 0)
{
if (x_5 == 0)
{
if (x_6 == 0)
{
goto block_35;
}
else
{
x_36 = x_40;
goto block_37;
}
}
else
{
x_36 = x_40;
goto block_37;
}
}
else
{
x_36 = x_40;
goto block_37;
}
block_12:
{
uint16_t x_9; uint8_t x_10; 
x_9 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_10 = lean_int16_dec_le(x_7, x_9);
if (x_10 == 0)
{
uint16_t x_11; 
x_11 = lean_int16_add(x_8, x_7);
return x_11;
}
else
{
return x_8;
}
}
block_18:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_4, x_14);
if (x_15 == 0)
{
x_8 = x_13;
goto block_12;
}
else
{
uint16_t x_16; uint16_t x_17; 
x_16 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1;
x_17 = lean_int16_add(x_13, x_16);
x_8 = x_17;
goto block_12;
}
}
block_23:
{
if (x_20 == 0)
{
x_13 = x_19;
goto block_18;
}
else
{
uint16_t x_21; uint16_t x_22; 
x_21 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0;
x_22 = lean_int16_add(x_19, x_21);
x_13 = x_22;
goto block_18;
}
}
block_32:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_string_length(x_2);
x_27 = lean_nat_sub(x_26, x_24);
x_28 = lean_nat_dec_eq(x_4, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
x_19 = x_25;
x_20 = x_28;
goto block_23;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_string_length(x_1);
x_30 = lean_nat_sub(x_29, x_24);
x_31 = lean_nat_dec_eq(x_3, x_30);
lean_dec(x_30);
x_19 = x_25;
x_20 = x_31;
goto block_23;
}
}
block_35:
{
uint16_t x_34; 
x_34 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1;
x_25 = x_34;
goto block_32;
}
block_37:
{
if (x_36 == 0)
{
x_25 = x_33;
goto block_32;
}
else
{
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint16_t x_10; uint16_t x_11; lean_object* x_12; 
x_8 = lean_unbox(x_5);
x_9 = lean_unbox(x_6);
x_10 = lean_unbox(x_7);
x_11 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(x_1, x_2, x_3, x_4, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(x_11);
return x_12;
}
}
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; lean_object* x_4; uint16_t x_5; 
x_2 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_3 = lean_box(x_2);
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* x_1, lean_object* x_2, uint16_t x_3) {
_start:
{
uint16_t x_4; uint8_t x_5; 
x_4 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_5 = lean_int16_dec_le(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_1, x_2);
if (x_6 == 0)
{
return x_3;
}
else
{
uint16_t x_7; uint16_t x_8; 
x_7 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
x_8 = lean_int16_add(x_3, x_7);
return x_8;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, uint16_t x_8) {
_start:
{
uint16_t x_9; uint8_t x_10; 
x_9 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_10 = lean_int16_dec_le(x_8, x_9);
if (x_10 == 0)
{
uint16_t x_11; uint16_t x_12; uint16_t x_13; lean_object* x_14; lean_object* x_15; uint16_t x_16; uint16_t x_17; 
x_11 = l_instInhabitedInt16;
x_12 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
x_13 = lean_int16_add(x_8, x_12);
x_14 = lean_box(x_11);
x_15 = lean_array_get_borrowed(x_14, x_7, x_4);
x_16 = lean_unbox(x_15);
x_17 = lean_int16_sub(x_13, x_16);
return x_17;
}
else
{
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint16_t x_11; uint16_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = lean_unbox(x_8);
x_12 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_11);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(x_12);
return x_13;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint16_t x_7, uint16_t x_8) {
_start:
{
uint16_t x_9; uint16_t x_13; uint8_t x_14; 
x_13 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_14 = lean_int16_dec_le(x_8, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_int16_dec_eq(x_7, x_13);
if (x_15 == 0)
{
x_9 = x_7;
goto block_12;
}
else
{
lean_object* x_16; uint16_t x_17; 
x_16 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3;
x_17 = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(x_16);
x_9 = x_17;
goto block_12;
}
}
else
{
return x_8;
}
block_12:
{
uint16_t x_10; uint16_t x_11; 
x_10 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
x_11 = lean_int16_add(x_8, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint16_t x_11; uint16_t x_12; uint16_t x_13; lean_object* x_14; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = lean_unbox(x_7);
x_12 = lean_unbox(x_8);
x_13 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_box(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 2);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_dec(x_10);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint16_t x_18; lean_object* x_19; uint16_t x_20; uint16_t x_21; lean_object* x_22; lean_object* x_38; uint16_t x_39; uint16_t x_40; uint16_t x_43; uint8_t x_106; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_16 = x_9;
} else {
 lean_dec_ref(x_9);
 x_16 = lean_box(0);
}
x_17 = 0;
x_18 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_19 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_dec_le(x_19, x_10);
if (x_106 == 0)
{
x_43 = x_18;
goto block_105;
}
else
{
lean_object* x_107; uint16_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint16_t x_120; uint16_t x_121; uint8_t x_122; 
x_107 = lean_nat_sub(x_10, x_19);
x_108 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_109 = lean_string_length(x_1);
x_110 = lean_nat_mul(x_2, x_109);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_nat_mul(x_110, x_111);
lean_dec(x_110);
x_113 = lean_nat_mul(x_107, x_111);
lean_dec(x_107);
x_114 = lean_nat_add(x_112, x_113);
lean_dec(x_113);
lean_dec(x_112);
x_115 = lean_box(x_108);
x_116 = lean_array_get_borrowed(x_115, x_14, x_114);
x_117 = lean_nat_add(x_114, x_19);
lean_dec(x_114);
x_118 = lean_box(x_108);
x_119 = lean_array_get_borrowed(x_118, x_14, x_117);
lean_dec(x_117);
x_120 = lean_unbox(x_116);
x_121 = lean_unbox(x_119);
x_122 = lean_int16_dec_le(x_120, x_121);
if (x_122 == 0)
{
uint16_t x_123; 
x_123 = lean_unbox(x_116);
x_43 = x_123;
goto block_105;
}
else
{
uint16_t x_124; 
x_124 = lean_unbox(x_119);
x_43 = x_124;
goto block_105;
}
}
block_37:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_string_length(x_1);
x_24 = lean_nat_mul(x_2, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_mul(x_24, x_25);
lean_dec(x_24);
x_27 = lean_nat_mul(x_10, x_25);
x_28 = lean_nat_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = lean_box(x_20);
x_30 = lean_array_set(x_14, x_28, x_29);
x_31 = lean_nat_add(x_28, x_19);
lean_dec(x_28);
x_32 = lean_box(x_21);
x_33 = lean_array_set(x_30, x_31, x_32);
lean_dec(x_31);
if (lean_is_scalar(x_16)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_16;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
x_35 = lean_nat_add(x_10, x_12);
lean_dec(x_10);
x_9 = x_34;
x_10 = x_35;
goto _start;
}
block_42:
{
uint16_t x_41; 
x_41 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(x_7, x_10, x_40);
x_20 = x_39;
x_21 = x_41;
x_22 = x_38;
goto block_37;
}
block_105:
{
uint32_t x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_44 = lean_string_utf8_get(x_3, x_2);
x_45 = lean_string_utf8_get(x_1, x_10);
x_46 = lean_box(x_17);
x_47 = lean_array_get_borrowed(x_46, x_4, x_2);
x_48 = lean_box(x_17);
x_49 = lean_array_get_borrowed(x_48, x_5, x_10);
x_50 = lean_unbox(x_47);
x_51 = lean_unbox(x_49);
x_52 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(x_44, x_45, x_50, x_51);
if (x_52 == 0)
{
x_20 = x_43;
x_21 = x_18;
x_22 = x_15;
goto block_37;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_19, x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint16_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint16_t x_62; uint16_t x_63; lean_object* x_64; lean_object* x_65; uint16_t x_66; uint16_t x_67; uint8_t x_68; 
x_54 = lean_string_length(x_1);
x_55 = lean_nat_mul(x_2, x_54);
x_56 = lean_nat_add(x_55, x_10);
lean_dec(x_55);
x_57 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
x_58 = lean_box(x_57);
x_59 = lean_array_set(x_15, x_56, x_58);
lean_dec(x_56);
x_60 = lean_unbox(x_47);
x_61 = lean_unbox(x_49);
x_62 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(x_3, x_1, x_2, x_10, x_60, x_61, x_18);
x_63 = l_instInhabitedInt16;
x_64 = lean_box(x_63);
x_65 = lean_array_get_borrowed(x_64, x_6, x_10);
x_66 = lean_unbox(x_65);
x_67 = lean_int16_sub(x_62, x_66);
x_68 = lean_int16_dec_eq(x_67, x_18);
if (x_68 == 0)
{
x_20 = x_43;
x_21 = x_67;
x_22 = x_59;
goto block_37;
}
else
{
lean_object* x_69; uint16_t x_70; 
x_69 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3;
x_70 = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(x_69);
x_20 = x_43;
x_21 = x_70;
x_22 = x_59;
goto block_37;
}
}
else
{
uint16_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint16_t x_79; uint16_t x_80; uint16_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint16_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; uint16_t x_95; uint16_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint16_t x_102; uint16_t x_103; uint8_t x_104; 
x_71 = l_instInhabitedInt16;
x_72 = lean_nat_sub(x_2, x_19);
x_73 = lean_nat_sub(x_10, x_19);
x_74 = lean_string_length(x_1);
x_75 = lean_nat_mul(x_72, x_74);
lean_dec(x_72);
x_76 = lean_nat_add(x_75, x_73);
x_77 = lean_box(x_71);
x_78 = lean_array_get_borrowed(x_77, x_15, x_76);
lean_dec(x_76);
x_79 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
x_80 = lean_unbox(x_78);
x_81 = lean_int16_add(x_80, x_79);
x_82 = lean_nat_mul(x_2, x_74);
x_83 = lean_nat_add(x_82, x_10);
lean_dec(x_82);
x_84 = lean_box(x_81);
x_85 = lean_array_set(x_15, x_83, x_84);
lean_dec(x_83);
x_86 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_87 = lean_unsigned_to_nat(2u);
x_88 = lean_nat_mul(x_75, x_87);
lean_dec(x_75);
x_89 = lean_nat_mul(x_73, x_87);
lean_dec(x_73);
x_90 = lean_nat_add(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
x_91 = lean_box(x_86);
x_92 = lean_array_get_borrowed(x_91, x_14, x_90);
x_93 = lean_unbox(x_47);
x_94 = lean_unbox(x_49);
x_95 = lean_unbox(x_92);
x_96 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(x_3, x_1, x_2, x_10, x_93, x_94, x_6, x_95);
x_97 = lean_nat_add(x_90, x_19);
lean_dec(x_90);
x_98 = lean_box(x_86);
x_99 = lean_array_get_borrowed(x_98, x_14, x_97);
lean_dec(x_97);
x_100 = lean_unbox(x_47);
x_101 = lean_unbox(x_49);
x_102 = lean_unbox(x_99);
x_103 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(x_3, x_1, x_2, x_10, x_100, x_101, x_81, x_102);
x_104 = lean_int16_dec_le(x_96, x_103);
if (x_104 == 0)
{
x_38 = x_85;
x_39 = x_43;
x_40 = x_96;
goto block_42;
}
else
{
x_38 = x_85;
x_39 = x_43;
x_40 = x_103;
goto block_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_dec(x_11);
return x_10;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_11);
x_18 = lean_nat_sub(x_17, x_16);
lean_dec(x_17);
x_19 = lean_nat_sub(x_2, x_18);
lean_dec(x_18);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
lean_inc(x_11);
x_21 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11);
lean_dec_ref(x_20);
x_22 = lean_nat_add(x_11, x_13);
lean_dec(x_11);
x_10 = x_21;
x_11 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_1, x_11);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = lean_nat_sub(x_2, x_28);
lean_dec(x_28);
lean_inc(x_11);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_inc(x_11);
x_32 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_30, x_31, x_11);
lean_dec_ref(x_30);
x_33 = lean_nat_add(x_11, x_13);
lean_dec(x_11);
x_10 = x_32;
x_11 = x_33;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_dec(x_11);
return x_10;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_11);
x_18 = lean_nat_sub(x_17, x_16);
lean_dec(x_17);
x_19 = lean_nat_sub(x_8, x_18);
lean_dec(x_18);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
lean_inc(x_11);
x_21 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_20, x_10, x_11);
lean_dec_ref(x_20);
x_22 = lean_nat_add(x_11, x_13);
lean_dec(x_11);
x_23 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(x_7, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_7, x_11);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = lean_nat_sub(x_8, x_28);
lean_dec(x_28);
lean_inc(x_11);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_inc(x_11);
x_32 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_30, x_31, x_11);
lean_dec_ref(x_30);
x_33 = lean_nat_add(x_11, x_13);
lean_dec(x_11);
x_34 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(x_7, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_32, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint16_t x_20; uint16_t x_21; uint8_t x_39; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_16 = x_9;
} else {
 lean_dec_ref(x_9);
 x_16 = lean_box(0);
}
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_4, x_18);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_box(x_17);
x_41 = lean_array_get_borrowed(x_40, x_1, x_4);
x_42 = lean_unbox(x_41);
if (x_42 == 2)
{
uint16_t x_43; uint16_t x_44; uint16_t x_45; uint16_t x_46; 
lean_dec(x_14);
lean_dec(x_10);
x_43 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0;
x_44 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
x_45 = lean_unbox(x_12);
lean_dec(x_12);
x_46 = lean_int16_add(x_45, x_44);
lean_inc(x_4);
x_19 = x_4;
x_20 = x_46;
x_21 = x_43;
goto block_38;
}
else
{
uint16_t x_47; uint16_t x_48; 
x_47 = lean_unbox(x_12);
lean_dec(x_12);
x_48 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = x_10;
x_20 = x_47;
x_21 = x_48;
goto block_38;
}
}
else
{
uint16_t x_49; uint16_t x_50; 
x_49 = lean_unbox(x_12);
lean_dec(x_12);
x_50 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = x_10;
x_20 = x_49;
x_21 = x_50;
goto block_38;
}
block_38:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint16_t x_26; uint16_t x_27; uint16_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_box(x_17);
x_23 = lean_array_get_borrowed(x_22, x_1, x_4);
x_24 = lean_nat_dec_eq(x_4, x_18);
x_25 = lean_unbox(x_23);
x_26 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(x_25, x_24);
x_27 = lean_int16_add(x_21, x_26);
x_28 = lean_int16_add(x_27, x_20);
x_29 = lean_box(x_28);
x_30 = lean_array_set(x_15, x_4, x_29);
x_31 = lean_box(x_27);
if (lean_is_scalar(x_16)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_16;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_box(x_20);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
if (lean_is_scalar(x_11)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_11;
}
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_35;
x_4 = x_36;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint16_t x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint16_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_12 = lean_string_length(x_1);
x_13 = lean_string_length(x_2);
x_14 = lean_nat_mul(x_12, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_mul(x_14, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0;
x_19 = lean_box(x_18);
x_20 = lean_mk_array(x_14, x_19);
x_21 = lean_box(x_18);
x_22 = lean_mk_array(x_13, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_box(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_box(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(x_4, x_24, x_29, x_17);
lean_dec_ref(x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint16_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint16_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint16_t x_55; uint16_t x_56; uint8_t x_57; 
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_38 = lean_box(x_37);
x_39 = lean_mk_array(x_16, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_12);
lean_ctor_set(x_40, 2, x_23);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 0, x_39);
x_41 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(x_2, x_1, x_3, x_4, x_35, x_33, x_12, x_13, x_40, x_32, x_17);
lean_dec_ref(x_40);
lean_dec(x_33);
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_nat_sub(x_12, x_23);
x_44 = lean_nat_sub(x_13, x_23);
x_45 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_46 = lean_nat_mul(x_43, x_13);
lean_dec(x_43);
x_47 = lean_nat_mul(x_46, x_15);
lean_dec(x_46);
x_48 = lean_nat_mul(x_44, x_15);
lean_dec(x_44);
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_50 = lean_box(x_45);
x_51 = lean_array_get(x_50, x_42, x_49);
x_52 = lean_nat_add(x_49, x_23);
lean_dec(x_49);
x_53 = lean_box(x_45);
x_54 = lean_array_get(x_53, x_42, x_52);
lean_dec(x_52);
lean_dec(x_42);
x_55 = lean_unbox(x_51);
x_56 = lean_unbox(x_54);
x_57 = lean_int16_dec_le(x_55, x_56);
if (x_57 == 0)
{
uint16_t x_58; 
lean_dec(x_54);
x_58 = lean_unbox(x_51);
lean_dec(x_51);
x_5 = x_58;
goto block_11;
}
else
{
uint16_t x_59; 
lean_dec(x_51);
x_59 = lean_unbox(x_54);
lean_dec(x_54);
x_5 = x_59;
goto block_11;
}
}
else
{
lean_object* x_60; uint16_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint16_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint16_t x_80; uint16_t x_81; uint8_t x_82; 
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_dec(x_32);
x_61 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_62 = lean_box(x_61);
x_63 = lean_mk_array(x_16, x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_17);
lean_ctor_set(x_64, 1, x_12);
lean_ctor_set(x_64, 2, x_23);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_20);
x_66 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(x_2, x_1, x_3, x_4, x_60, x_33, x_12, x_13, x_64, x_65, x_17);
lean_dec_ref(x_64);
lean_dec(x_33);
lean_dec(x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_nat_sub(x_12, x_23);
x_69 = lean_nat_sub(x_13, x_23);
x_70 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default;
x_71 = lean_nat_mul(x_68, x_13);
lean_dec(x_68);
x_72 = lean_nat_mul(x_71, x_15);
lean_dec(x_71);
x_73 = lean_nat_mul(x_69, x_15);
lean_dec(x_69);
x_74 = lean_nat_add(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
x_75 = lean_box(x_70);
x_76 = lean_array_get(x_75, x_67, x_74);
x_77 = lean_nat_add(x_74, x_23);
lean_dec(x_74);
x_78 = lean_box(x_70);
x_79 = lean_array_get(x_78, x_67, x_77);
lean_dec(x_77);
lean_dec(x_67);
x_80 = lean_unbox(x_76);
x_81 = lean_unbox(x_79);
x_82 = lean_int16_dec_le(x_80, x_81);
if (x_82 == 0)
{
uint16_t x_83; 
lean_dec(x_79);
x_83 = lean_unbox(x_76);
lean_dec(x_76);
x_5 = x_83;
goto block_11;
}
else
{
uint16_t x_84; 
lean_dec(x_76);
x_84 = lean_unbox(x_79);
lean_dec(x_79);
x_5 = x_84;
goto block_11;
}
}
block_11:
{
uint16_t x_6; uint8_t x_7; 
x_6 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
x_7 = lean_int16_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_int16_to_int(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0;
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; lean_object* x_11; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_string_utf8_byte_size(x_1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_string_length(x_2);
x_33 = lean_string_length(x_1);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_String_charactersIn(x_1, x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
return x_36;
}
else
{
if (x_31 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(x_1);
x_38 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(x_2);
x_39 = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(x_1, x_2, x_37, x_38);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_nat_dec_eq(x_33, x_32);
if (x_41 == 0)
{
x_11 = x_40;
goto block_28;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2;
x_43 = lean_int_mul(x_40, x_42);
lean_dec(x_40);
x_11 = x_43;
goto block_28;
}
}
else
{
lean_object* x_44; 
lean_dec(x_39);
x_44 = lean_box(0);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = lean_box(0);
return x_45;
}
}
}
else
{
lean_object* x_46; 
x_46 = lean_box(0);
return x_46;
}
}
else
{
lean_object* x_47; 
x_47 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3;
return x_47;
}
block_10:
{
uint8_t x_5; 
x_5 = lean_float_decLe(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_float(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box_float(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
block_28:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; double x_21; lean_object* x_22; double x_23; double x_24; double x_25; double x_26; uint8_t x_27; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_string_length(x_1);
x_14 = lean_nat_mul(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_13, x_15);
x_17 = lean_nat_mul(x_13, x_16);
lean_dec(x_16);
x_18 = lean_nat_shiftr(x_17, x_15);
lean_dec(x_17);
x_19 = lean_nat_sub(x_18, x_15);
lean_dec(x_18);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_19);
lean_dec(x_14);
x_21 = l_Float_ofInt(x_11);
lean_dec(x_11);
x_22 = lean_nat_to_int(x_20);
x_23 = l_Float_ofInt(x_22);
lean_dec(x_22);
x_24 = lean_float_div(x_21, x_23);
x_25 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0;
x_26 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1;
x_27 = lean_float_decLe(x_26, x_24);
if (x_27 == 0)
{
x_3 = x_25;
x_4 = x_26;
goto block_10;
}
else
{
x_3 = x_25;
x_4 = x_24;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* x_1, lean_object* x_2, double x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; double x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox_float(x_5);
lean_dec(x_5);
x_7 = lean_float_decLt(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
double x_4; lean_object* x_5; 
x_4 = lean_unbox_float(x_3);
lean_dec_ref(x_3);
x_5 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_2, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* x_1, lean_object* x_2, double x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec_ref(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
double x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_float(x_3);
lean_dec_ref(x_3);
x_5 = l_Lean_FuzzyMatching_fuzzyMatch(x_1, x_2, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_FuzzyMatching(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10();
lean_mark_persistent(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10);
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__11 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__11();
lean_mark_persistent(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__11);
l_Lean_FuzzyMatching_instInhabitedCharRole_default = _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default();
l_Lean_FuzzyMatching_instInhabitedCharRole = _init_l_Lean_FuzzyMatching_instInhabitedCharRole();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0);
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__1 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__1();
lean_mark_persistent(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__1);
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default___closed__0();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore_default();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3();
lean_mark_persistent(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1 = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1();
l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0 = _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0();
l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1 = _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1();
l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2 = _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2();
lean_mark_persistent(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1 = _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1);
l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3 = _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3();
lean_mark_persistent(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
