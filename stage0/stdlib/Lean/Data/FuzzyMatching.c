// Lean compiler output
// Module: Lean.Data.FuzzyMatching
// Imports: public import Init.Data.Range.Polymorphic.Iterators public import Init.Data.Range.Polymorphic.Nat public import Init.Data.OfScientific public import Init.Data.Option.Coe public import Init.Data.Range import Lean.Server.Completion.CompletionUtils
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
uint16_t lean_int16_of_nat(lean_object*);
uint16_t lean_int16_neg(uint16_t);
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint16_t lean_int16_add(uint16_t, uint16_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern uint16_t l_instInhabitedInt16;
uint16_t lean_int16_sub(uint16_t, uint16_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int16_to_int(uint16_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLe(double, double);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
double l_Float_ofInt(lean_object*);
double lean_float_div(double, double);
uint8_t l_String_charactersIn(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value),((lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9_value;
static const lean_array_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0;
LEAN_EXPORT uint16_t l_Lean_FuzzyMatching_instInhabitedScore_default;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore;
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0;
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful;
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Data.FuzzyMatching"};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0_value;
static const lean_string_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Data.FuzzyMatching.0.Lean.FuzzyMatching.Score.ofInt16!"};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1_value;
static const lean_string_object l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: x != awful.inner\n  "};
static const lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2 = (const lean_object*)&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2_value;
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object*, lean_object*, lean_object*, lean_object*, uint16_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0;
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t, uint32_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0;
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1;
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object*);
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0;
static lean_once_cell_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1;
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object*);
static lean_once_cell_t l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0;
static lean_once_cell_t l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1;
static lean_once_cell_t l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
static lean_once_cell_t l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(lean_object* v___x_1_, lean_object* v_string_2_, lean_object* v___x_3_, lean_object* v_f_4_, lean_object* v_a_5_, lean_object* v_x_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; uint32_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint32_t v___x_13_; uint32_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_8_ = lean_nat_sub(v_a_5_, v___x_1_);
v___x_9_ = lean_string_utf8_get(v_string_2_, v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lean_box_uint32(v___x_9_);
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
v___x_12_ = lean_nat_sub(v_a_5_, v___x_3_);
v___x_13_ = lean_string_utf8_get(v_string_2_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_string_utf8_get(v_string_2_, v_a_5_);
v___x_15_ = lean_box_uint32(v___x_14_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
v___x_17_ = lean_box_uint32(v___x_13_);
v___x_18_ = lean_apply_3(v_f_4_, v___x_11_, v___x_17_, v___x_16_);
v___x_19_ = lean_array_push(v___y_7_, v___x_18_);
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed(lean_object* v___x_21_, lean_object* v_string_22_, lean_object* v___x_23_, lean_object* v_f_24_, lean_object* v_a_25_, lean_object* v_x_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(v___x_21_, v_string_22_, v___x_23_, v_f_24_, v_a_25_, v_x_26_, v___y_27_);
lean_dec(v_a_25_);
lean_dec(v___x_23_);
lean_dec_ref(v_string_22_);
lean_dec(v___x_21_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(lean_object* v_f_50_, lean_object* v_string_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_52_ = lean_string_utf8_byte_size(v_string_51_);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_nat_dec_eq(v___x_52_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = lean_string_length(v_string_51_);
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_dec_eq(v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v_result_58_; lean_object* v___x_59_; uint32_t v___x_60_; uint32_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_result_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint32_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint32_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_result_58_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_string_utf8_get(v_string_51_, v___x_53_);
v___x_61_ = lean_string_utf8_get(v_string_51_, v___x_56_);
v___x_62_ = lean_box_uint32(v___x_61_);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = lean_box_uint32(v___x_60_);
lean_inc_n(v_f_50_, 2);
v___x_65_ = lean_apply_3(v_f_50_, v___x_59_, v___x_64_, v___x_63_);
v_result_66_ = lean_array_push(v_result_58_, v___x_65_);
v___x_67_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9));
v___x_68_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v_string_51_);
v___f_69_ = lean_alloc_closure((void*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_69_, 0, v___x_68_);
lean_closure_set(v___f_69_, 1, v_string_51_);
lean_closure_set(v___f_69_, 2, v___x_56_);
lean_closure_set(v___f_69_, 3, v_f_50_);
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_55_);
lean_ctor_set(v___x_70_, 2, v___x_56_);
v___x_71_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_67_, v___x_70_, v___f_69_, v_result_66_, v___x_68_, lean_box(0), lean_box(0));
v___x_72_ = lean_nat_sub(v___x_55_, v___x_68_);
v___x_73_ = lean_string_utf8_get(v_string_51_, v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_box_uint32(v___x_73_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = lean_nat_sub(v___x_55_, v___x_56_);
v___x_77_ = lean_string_utf8_get(v_string_51_, v___x_76_);
lean_dec(v___x_76_);
lean_dec_ref(v_string_51_);
v___x_78_ = lean_box_uint32(v___x_77_);
v___x_79_ = lean_apply_3(v_f_50_, v___x_75_, v___x_78_, v___x_59_);
v___x_80_ = lean_array_push(v___x_71_, v___x_79_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; uint32_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_string_utf8_get(v_string_51_, v___x_53_);
lean_dec_ref(v_string_51_);
v___x_83_ = lean_box_uint32(v___x_82_);
v___x_84_ = lean_apply_3(v_f_50_, v___x_81_, v___x_83_, v___x_81_);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_86_ = lean_array_push(v___x_85_, v___x_84_);
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec_ref(v_string_51_);
lean_dec(v_f_50_);
v___x_87_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10));
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround(lean_object* v_00_u03b1_88_, lean_object* v_f_89_, lean_object* v_string_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(v_f_89_, v_string_90_);
return v___x_91_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(lean_object* v_a_92_, lean_object* v_b_93_, lean_object* v_aPos_94_, lean_object* v_bPos_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_string_utf8_at_end(v_a_92_, v_aPos_94_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; 
v___x_97_ = lean_string_utf8_at_end(v_b_93_, v_bPos_95_);
if (v___x_97_ == 0)
{
uint32_t v_ac_98_; uint32_t v_bc_99_; lean_object* v_bPos_100_; uint32_t v___y_102_; uint32_t v___y_103_; uint32_t v___y_109_; uint32_t v___x_116_; uint8_t v___x_117_; 
v_ac_98_ = lean_string_utf8_get_fast(v_a_92_, v_aPos_94_);
v_bc_99_ = lean_string_utf8_get_fast(v_b_93_, v_bPos_95_);
v_bPos_100_ = lean_string_utf8_next_fast(v_b_93_, v_bPos_95_);
lean_dec(v_bPos_95_);
v___x_116_ = 65;
v___x_117_ = lean_uint32_dec_le(v___x_116_, v_ac_98_);
if (v___x_117_ == 0)
{
v___y_109_ = v_ac_98_;
goto v___jp_108_;
}
else
{
uint32_t v___x_118_; uint8_t v___x_119_; 
v___x_118_ = 90;
v___x_119_ = lean_uint32_dec_le(v_ac_98_, v___x_118_);
if (v___x_119_ == 0)
{
v___y_109_ = v_ac_98_;
goto v___jp_108_;
}
else
{
uint32_t v___x_120_; uint32_t v___x_121_; 
v___x_120_ = 32;
v___x_121_ = lean_uint32_add(v_ac_98_, v___x_120_);
v___y_109_ = v___x_121_;
goto v___jp_108_;
}
}
v___jp_101_:
{
uint8_t v___x_104_; 
v___x_104_ = lean_uint32_dec_eq(v___y_102_, v___y_103_);
if (v___x_104_ == 0)
{
v_bPos_95_ = v_bPos_100_;
goto _start;
}
else
{
lean_object* v_aPos_106_; 
v_aPos_106_ = lean_string_utf8_next_fast(v_a_92_, v_aPos_94_);
lean_dec(v_aPos_94_);
v_aPos_94_ = v_aPos_106_;
v_bPos_95_ = v_bPos_100_;
goto _start;
}
}
v___jp_108_:
{
uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = 65;
v___x_111_ = lean_uint32_dec_le(v___x_110_, v_bc_99_);
if (v___x_111_ == 0)
{
v___y_102_ = v___y_109_;
v___y_103_ = v_bc_99_;
goto v___jp_101_;
}
else
{
uint32_t v___x_112_; uint8_t v___x_113_; 
v___x_112_ = 90;
v___x_113_ = lean_uint32_dec_le(v_bc_99_, v___x_112_);
if (v___x_113_ == 0)
{
v___y_102_ = v___y_109_;
v___y_103_ = v_bc_99_;
goto v___jp_101_;
}
else
{
uint32_t v___x_114_; uint32_t v___x_115_; 
v___x_114_ = 32;
v___x_115_ = lean_uint32_add(v_bc_99_, v___x_114_);
v___y_102_ = v___y_109_;
v___y_103_ = v___x_115_;
goto v___jp_101_;
}
}
}
}
else
{
lean_dec(v_bPos_95_);
lean_dec(v_aPos_94_);
return v___x_96_;
}
}
else
{
lean_dec(v_bPos_95_);
lean_dec(v_aPos_94_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go___boxed(lean_object* v_a_122_, lean_object* v_b_123_, lean_object* v_aPos_124_, lean_object* v_bPos_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_122_, v_b_123_, v_aPos_124_, v_bPos_125_);
lean_dec_ref(v_b_123_);
lean_dec_ref(v_a_122_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_128_, v_b_129_, v___x_130_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower___boxed(lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(v_a_132_, v_b_133_);
lean_dec_ref(v_b_133_);
lean_dec_ref(v_a_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx(uint8_t v_x_136_){
_start:
{
switch(v_x_136_)
{
case 0:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(0u);
return v___x_137_;
}
case 1:
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(1u);
return v___x_138_;
}
default: 
{
lean_object* v___x_139_; 
v___x_139_ = lean_unsigned_to_nat(2u);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___boxed(lean_object* v_x_140_){
_start:
{
uint8_t v_x_boxed_141_; lean_object* v_res_142_; 
v_x_boxed_141_ = lean_unbox(v_x_140_);
v_res_142_ = l_Lean_FuzzyMatching_CharType_ctorIdx(v_x_boxed_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_toCtorIdx(uint8_t v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_FuzzyMatching_CharType_ctorIdx(v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_toCtorIdx___boxed(lean_object* v_x_145_){
_start:
{
uint8_t v_x_4__boxed_146_; lean_object* v_res_147_; 
v_x_4__boxed_146_ = lean_unbox(v_x_145_);
v_res_147_ = l_Lean_FuzzyMatching_CharType_toCtorIdx(v_x_4__boxed_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg(lean_object* v_k_148_){
_start:
{
lean_inc(v_k_148_);
return v_k_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(lean_object* v_k_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_FuzzyMatching_CharType_ctorElim___redArg(v_k_149_);
lean_dec(v_k_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim(lean_object* v_motive_151_, lean_object* v_ctorIdx_152_, uint8_t v_t_153_, lean_object* v_h_154_, lean_object* v_k_155_){
_start:
{
lean_inc(v_k_155_);
return v_k_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___boxed(lean_object* v_motive_156_, lean_object* v_ctorIdx_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_k_160_){
_start:
{
uint8_t v_t_boxed_161_; lean_object* v_res_162_; 
v_t_boxed_161_ = lean_unbox(v_t_158_);
v_res_162_ = l_Lean_FuzzyMatching_CharType_ctorElim(v_motive_156_, v_ctorIdx_157_, v_t_boxed_161_, v_h_159_, v_k_160_);
lean_dec(v_k_160_);
lean_dec(v_ctorIdx_157_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg(lean_object* v_lower_163_){
_start:
{
lean_inc(v_lower_163_);
return v_lower_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(lean_object* v_lower_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_FuzzyMatching_CharType_lower_elim___redArg(v_lower_164_);
lean_dec(v_lower_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim(lean_object* v_motive_166_, uint8_t v_t_167_, lean_object* v_h_168_, lean_object* v_lower_169_){
_start:
{
lean_inc(v_lower_169_);
return v_lower_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___boxed(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_lower_173_){
_start:
{
uint8_t v_t_boxed_174_; lean_object* v_res_175_; 
v_t_boxed_174_ = lean_unbox(v_t_171_);
v_res_175_ = l_Lean_FuzzyMatching_CharType_lower_elim(v_motive_170_, v_t_boxed_174_, v_h_172_, v_lower_173_);
lean_dec(v_lower_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg(lean_object* v_upper_176_){
_start:
{
lean_inc(v_upper_176_);
return v_upper_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(lean_object* v_upper_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_FuzzyMatching_CharType_upper_elim___redArg(v_upper_177_);
lean_dec(v_upper_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim(lean_object* v_motive_179_, uint8_t v_t_180_, lean_object* v_h_181_, lean_object* v_upper_182_){
_start:
{
lean_inc(v_upper_182_);
return v_upper_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___boxed(lean_object* v_motive_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_upper_186_){
_start:
{
uint8_t v_t_boxed_187_; lean_object* v_res_188_; 
v_t_boxed_187_ = lean_unbox(v_t_184_);
v_res_188_ = l_Lean_FuzzyMatching_CharType_upper_elim(v_motive_183_, v_t_boxed_187_, v_h_185_, v_upper_186_);
lean_dec(v_upper_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg(lean_object* v_separator_189_){
_start:
{
lean_inc(v_separator_189_);
return v_separator_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg___boxed(lean_object* v_separator_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_FuzzyMatching_CharType_separator_elim___redArg(v_separator_190_);
lean_dec(v_separator_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim(lean_object* v_motive_192_, uint8_t v_t_193_, lean_object* v_h_194_, lean_object* v_separator_195_){
_start:
{
lean_inc(v_separator_195_);
return v_separator_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___boxed(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_separator_199_){
_start:
{
uint8_t v_t_boxed_200_; lean_object* v_res_201_; 
v_t_boxed_200_ = lean_unbox(v_t_197_);
v_res_201_ = l_Lean_FuzzyMatching_CharType_separator_elim(v_motive_196_, v_t_boxed_200_, v_h_198_, v_separator_199_);
lean_dec(v_separator_199_);
return v_res_201_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charType(uint32_t v_c_202_){
_start:
{
uint8_t v___y_212_; uint8_t v___y_215_; uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 65;
v___x_226_ = lean_uint32_dec_le(v___x_225_, v_c_202_);
if (v___x_226_ == 0)
{
goto v___jp_220_;
}
else
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 90;
v___x_228_ = lean_uint32_dec_le(v_c_202_, v___x_227_);
if (v___x_228_ == 0)
{
goto v___jp_220_;
}
else
{
goto v___jp_203_;
}
}
v___jp_203_:
{
uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 65;
v___x_205_ = lean_uint32_dec_le(v___x_204_, v_c_202_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
else
{
uint32_t v___x_207_; uint8_t v___x_208_; 
v___x_207_ = 90;
v___x_208_ = lean_uint32_dec_le(v_c_202_, v___x_207_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
else
{
uint8_t v___x_210_; 
v___x_210_ = 1;
return v___x_210_;
}
}
}
v___jp_211_:
{
if (v___y_212_ == 0)
{
uint8_t v___x_213_; 
v___x_213_ = 2;
return v___x_213_;
}
else
{
goto v___jp_203_;
}
}
v___jp_214_:
{
if (v___y_215_ == 0)
{
uint32_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = 48;
v___x_217_ = lean_uint32_dec_le(v___x_216_, v_c_202_);
if (v___x_217_ == 0)
{
v___y_212_ = v___x_217_;
goto v___jp_211_;
}
else
{
uint32_t v___x_218_; uint8_t v___x_219_; 
v___x_218_ = 57;
v___x_219_ = lean_uint32_dec_le(v_c_202_, v___x_218_);
v___y_212_ = v___x_219_;
goto v___jp_211_;
}
}
else
{
goto v___jp_203_;
}
}
v___jp_220_:
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 97;
v___x_222_ = lean_uint32_dec_le(v___x_221_, v_c_202_);
if (v___x_222_ == 0)
{
v___y_215_ = v___x_222_;
goto v___jp_214_;
}
else
{
uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 122;
v___x_224_ = lean_uint32_dec_le(v_c_202_, v___x_223_);
v___y_215_ = v___x_224_;
goto v___jp_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charType___boxed(lean_object* v_c_229_){
_start:
{
uint32_t v_c_boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_c_boxed_230_ = lean_unbox_uint32(v_c_229_);
lean_dec(v_c_229_);
v_res_231_ = l_Lean_FuzzyMatching_charType(v_c_boxed_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx(uint8_t v_x_233_){
_start:
{
switch(v_x_233_)
{
case 0:
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
return v___x_234_;
}
case 1:
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(1u);
return v___x_235_;
}
default: 
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(2u);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___boxed(lean_object* v_x_237_){
_start:
{
uint8_t v_x_boxed_238_; lean_object* v_res_239_; 
v_x_boxed_238_ = lean_unbox(v_x_237_);
v_res_239_ = l_Lean_FuzzyMatching_CharRole_ctorIdx(v_x_boxed_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_toCtorIdx(uint8_t v_x_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_FuzzyMatching_CharRole_ctorIdx(v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_toCtorIdx___boxed(lean_object* v_x_242_){
_start:
{
uint8_t v_x_4__boxed_243_; lean_object* v_res_244_; 
v_x_4__boxed_243_ = lean_unbox(v_x_242_);
v_res_244_ = l_Lean_FuzzyMatching_CharRole_toCtorIdx(v_x_4__boxed_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(lean_object* v_k_245_){
_start:
{
lean_inc(v_k_245_);
return v_k_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(lean_object* v_k_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(v_k_246_);
lean_dec(v_k_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, uint8_t v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
lean_inc(v_k_252_);
return v_k_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object* v_motive_253_, lean_object* v_ctorIdx_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_k_257_){
_start:
{
uint8_t v_t_boxed_258_; lean_object* v_res_259_; 
v_t_boxed_258_ = lean_unbox(v_t_255_);
v_res_259_ = l_Lean_FuzzyMatching_CharRole_ctorElim(v_motive_253_, v_ctorIdx_254_, v_t_boxed_258_, v_h_256_, v_k_257_);
lean_dec(v_k_257_);
lean_dec(v_ctorIdx_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object* v_head_260_){
_start:
{
lean_inc(v_head_260_);
return v_head_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object* v_head_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(v_head_261_);
lean_dec(v_head_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object* v_motive_263_, uint8_t v_t_264_, lean_object* v_h_265_, lean_object* v_head_266_){
_start:
{
lean_inc(v_head_266_);
return v_head_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object* v_motive_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_head_270_){
_start:
{
uint8_t v_t_boxed_271_; lean_object* v_res_272_; 
v_t_boxed_271_ = lean_unbox(v_t_268_);
v_res_272_ = l_Lean_FuzzyMatching_CharRole_head_elim(v_motive_267_, v_t_boxed_271_, v_h_269_, v_head_270_);
lean_dec(v_head_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object* v_tail_273_){
_start:
{
lean_inc(v_tail_273_);
return v_tail_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object* v_tail_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(v_tail_274_);
lean_dec(v_tail_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object* v_motive_276_, uint8_t v_t_277_, lean_object* v_h_278_, lean_object* v_tail_279_){
_start:
{
lean_inc(v_tail_279_);
return v_tail_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_tail_283_){
_start:
{
uint8_t v_t_boxed_284_; lean_object* v_res_285_; 
v_t_boxed_284_ = lean_unbox(v_t_281_);
v_res_285_ = l_Lean_FuzzyMatching_CharRole_tail_elim(v_motive_280_, v_t_boxed_284_, v_h_282_, v_tail_283_);
lean_dec(v_tail_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object* v_separator_286_){
_start:
{
lean_inc(v_separator_286_);
return v_separator_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object* v_separator_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(v_separator_287_);
lean_dec(v_separator_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object* v_motive_289_, uint8_t v_t_290_, lean_object* v_h_291_, lean_object* v_separator_292_){
_start:
{
lean_inc(v_separator_292_);
return v_separator_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object* v_motive_293_, lean_object* v_t_294_, lean_object* v_h_295_, lean_object* v_separator_296_){
_start:
{
uint8_t v_t_boxed_297_; lean_object* v_res_298_; 
v_t_boxed_297_ = lean_unbox(v_t_294_);
v_res_298_ = l_Lean_FuzzyMatching_CharRole_separator_elim(v_motive_293_, v_t_boxed_297_, v_h_295_, v_separator_296_);
lean_dec(v_separator_296_);
return v_res_298_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default(void){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole(void){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object* v_prev_x3f_301_, uint8_t v_curr_302_, lean_object* v_next_x3f_303_){
_start:
{
if (v_curr_302_ == 2)
{
uint8_t v___x_304_; 
v___x_304_ = 2;
return v___x_304_;
}
else
{
if (lean_obj_tag(v_prev_x3f_301_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
else
{
lean_object* v_val_306_; uint8_t v___x_307_; 
v_val_306_ = lean_ctor_get(v_prev_x3f_301_, 0);
v___x_307_ = lean_unbox(v_val_306_);
if (v___x_307_ == 2)
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
else
{
if (v_curr_302_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 1;
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = lean_unbox(v_val_306_);
if (v___x_310_ == 1)
{
if (lean_obj_tag(v_next_x3f_303_) == 1)
{
lean_object* v_val_311_; uint8_t v___x_312_; 
v_val_311_ = lean_ctor_get(v_next_x3f_303_, 0);
v___x_312_ = lean_unbox(v_val_311_);
if (v___x_312_ == 0)
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = 1;
return v___x_314_;
}
}
else
{
uint8_t v___x_315_; 
v___x_315_ = 1;
return v___x_315_;
}
}
else
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object* v_prev_x3f_317_, lean_object* v_curr_318_, lean_object* v_next_x3f_319_){
_start:
{
uint8_t v_curr_boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_curr_boxed_320_ = lean_unbox(v_curr_318_);
v_res_321_ = l_Lean_FuzzyMatching_charRole(v_prev_x3f_317_, v_curr_boxed_320_, v_next_x3f_319_);
lean_dec(v_next_x3f_319_);
lean_dec(v_prev_x3f_317_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_string_323_, lean_object* v_range_324_, lean_object* v_b_325_, lean_object* v_i_326_){
_start:
{
lean_object* v_stop_327_; lean_object* v_step_328_; uint8_t v___y_330_; uint8_t v___x_335_; 
v_stop_327_ = lean_ctor_get(v_range_324_, 1);
v_step_328_ = lean_ctor_get(v_range_324_, 2);
v___x_335_ = lean_nat_dec_lt(v_i_326_, v_stop_327_);
if (v___x_335_ == 0)
{
lean_dec(v_i_326_);
return v_b_325_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v_i_326_, v___x_336_);
v___x_338_ = lean_string_utf8_get(v_string_323_, v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = l_Lean_FuzzyMatching_charType(v___x_338_);
if (v___x_339_ == 2)
{
uint8_t v___x_340_; 
v___x_340_ = 2;
v___y_330_ = v___x_340_;
goto v___jp_329_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; uint32_t v___x_343_; uint8_t v___x_344_; 
v___x_341_ = lean_unsigned_to_nat(2u);
v___x_342_ = lean_nat_sub(v_i_326_, v___x_341_);
v___x_343_ = lean_string_utf8_get(v_string_323_, v___x_342_);
lean_dec(v___x_342_);
v___x_344_ = l_Lean_FuzzyMatching_charType(v___x_343_);
if (v___x_344_ == 2)
{
uint8_t v___x_345_; 
v___x_345_ = 0;
v___y_330_ = v___x_345_;
goto v___jp_329_;
}
else
{
if (v___x_339_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 1;
v___y_330_ = v___x_346_;
goto v___jp_329_;
}
else
{
if (v___x_344_ == 1)
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_string_utf8_get(v_string_323_, v_i_326_);
v___x_348_ = l_Lean_FuzzyMatching_charType(v___x_347_);
if (v___x_348_ == 0)
{
uint8_t v___x_349_; 
v___x_349_ = 0;
v___y_330_ = v___x_349_;
goto v___jp_329_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = 1;
v___y_330_ = v___x_350_;
goto v___jp_329_;
}
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 0;
v___y_330_ = v___x_351_;
goto v___jp_329_;
}
}
}
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_box(v___y_330_);
v___x_332_ = lean_array_push(v_b_325_, v___x_331_);
v___x_333_ = lean_nat_add(v_i_326_, v_step_328_);
lean_dec(v_i_326_);
v_b_325_ = v___x_332_;
v_i_326_ = v___x_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_string_352_, lean_object* v_range_353_, lean_object* v_b_354_, lean_object* v_i_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_352_, v_range_353_, v_b_354_, v_i_355_);
lean_dec_ref(v_range_353_);
lean_dec_ref(v_string_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object* v_string_357_, lean_object* v_range_358_, lean_object* v_b_359_, lean_object* v_i_360_){
_start:
{
lean_object* v_stop_361_; lean_object* v_step_362_; uint8_t v___y_364_; uint8_t v___x_369_; 
v_stop_361_ = lean_ctor_get(v_range_358_, 1);
v_step_362_ = lean_ctor_get(v_range_358_, 2);
v___x_369_ = lean_nat_dec_lt(v_i_360_, v_stop_361_);
if (v___x_369_ == 0)
{
return v_b_359_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_sub(v_i_360_, v___x_370_);
v___x_372_ = lean_string_utf8_get(v_string_357_, v___x_371_);
lean_dec(v___x_371_);
v___x_373_ = l_Lean_FuzzyMatching_charType(v___x_372_);
if (v___x_373_ == 2)
{
uint8_t v___x_374_; 
v___x_374_ = 2;
v___y_364_ = v___x_374_;
goto v___jp_363_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(2u);
v___x_376_ = lean_nat_sub(v_i_360_, v___x_375_);
v___x_377_ = lean_string_utf8_get(v_string_357_, v___x_376_);
lean_dec(v___x_376_);
v___x_378_ = l_Lean_FuzzyMatching_charType(v___x_377_);
if (v___x_378_ == 2)
{
uint8_t v___x_379_; 
v___x_379_ = 0;
v___y_364_ = v___x_379_;
goto v___jp_363_;
}
else
{
if (v___x_373_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = 1;
v___y_364_ = v___x_380_;
goto v___jp_363_;
}
else
{
if (v___x_378_ == 1)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_string_utf8_get(v_string_357_, v_i_360_);
v___x_382_ = l_Lean_FuzzyMatching_charType(v___x_381_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = 0;
v___y_364_ = v___x_383_;
goto v___jp_363_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 1;
v___y_364_ = v___x_384_;
goto v___jp_363_;
}
}
else
{
uint8_t v___x_385_; 
v___x_385_ = 0;
v___y_364_ = v___x_385_;
goto v___jp_363_;
}
}
}
}
}
v___jp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_box(v___y_364_);
v___x_366_ = lean_array_push(v_b_359_, v___x_365_);
v___x_367_ = lean_nat_add(v_i_360_, v_step_362_);
v___x_368_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_357_, v_range_358_, v___x_366_, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object* v_string_386_, lean_object* v_range_387_, lean_object* v_b_388_, lean_object* v_i_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_386_, v_range_387_, v_b_388_, v_i_389_);
lean_dec(v_i_389_);
lean_dec_ref(v_range_387_);
lean_dec_ref(v_string_386_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object* v_prev_x3f_391_, uint32_t v_curr_392_, lean_object* v_next_x3f_393_){
_start:
{
lean_object* v___y_395_; uint8_t v___y_396_; lean_object* v___y_397_; lean_object* v___y_412_; 
if (lean_obj_tag(v_prev_x3f_391_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_box(0);
v___y_412_ = v___x_426_;
goto v___jp_411_;
}
else
{
lean_object* v_val_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
v_val_427_ = lean_ctor_get(v_prev_x3f_391_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_prev_x3f_391_);
if (v_isSharedCheck_437_ == 0)
{
v___x_429_ = v_prev_x3f_391_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_val_427_);
lean_dec(v_prev_x3f_391_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint32_t v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_431_ = lean_unbox_uint32(v_val_427_);
lean_dec(v_val_427_);
v___x_432_ = l_Lean_FuzzyMatching_charType(v___x_431_);
v___x_433_ = lean_box(v___x_432_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_433_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
v___y_412_ = v___x_435_;
goto v___jp_411_;
}
}
}
v___jp_394_:
{
if (v___y_396_ == 2)
{
uint8_t v___x_398_; 
lean_dec(v___y_397_);
lean_dec(v___y_395_);
v___x_398_ = 2;
return v___x_398_;
}
else
{
if (lean_obj_tag(v___y_395_) == 0)
{
uint8_t v___x_399_; 
lean_dec(v___y_397_);
v___x_399_ = 0;
return v___x_399_;
}
else
{
lean_object* v_val_400_; uint8_t v___x_401_; 
v_val_400_ = lean_ctor_get(v___y_395_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v___y_395_);
v___x_401_ = lean_unbox(v_val_400_);
if (v___x_401_ == 2)
{
uint8_t v___x_402_; 
lean_dec(v_val_400_);
lean_dec(v___y_397_);
v___x_402_ = 0;
return v___x_402_;
}
else
{
if (v___y_396_ == 0)
{
uint8_t v___x_403_; 
lean_dec(v_val_400_);
lean_dec(v___y_397_);
v___x_403_ = 1;
return v___x_403_;
}
else
{
uint8_t v___x_404_; 
v___x_404_ = lean_unbox(v_val_400_);
lean_dec(v_val_400_);
if (v___x_404_ == 1)
{
if (lean_obj_tag(v___y_397_) == 1)
{
lean_object* v_val_405_; uint8_t v___x_406_; 
v_val_405_ = lean_ctor_get(v___y_397_, 0);
lean_inc(v_val_405_);
lean_dec_ref(v___y_397_);
v___x_406_ = lean_unbox(v_val_405_);
lean_dec(v_val_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 1;
return v___x_408_;
}
}
else
{
uint8_t v___x_409_; 
lean_dec(v___y_397_);
v___x_409_ = 1;
return v___x_409_;
}
}
else
{
uint8_t v___x_410_; 
lean_dec(v___y_397_);
v___x_410_ = 0;
return v___x_410_;
}
}
}
}
}
}
v___jp_411_:
{
uint8_t v___x_413_; 
v___x_413_ = l_Lean_FuzzyMatching_charType(v_curr_392_);
if (lean_obj_tag(v_next_x3f_393_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
v___y_395_ = v___y_412_;
v___y_396_ = v___x_413_;
v___y_397_ = v___x_414_;
goto v___jp_394_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_425_; 
v_val_415_ = lean_ctor_get(v_next_x3f_393_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_next_x3f_393_);
if (v_isSharedCheck_425_ == 0)
{
v___x_417_ = v_next_x3f_393_;
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v_next_x3f_393_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint32_t v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_419_ = lean_unbox_uint32(v_val_415_);
lean_dec(v_val_415_);
v___x_420_ = l_Lean_FuzzyMatching_charType(v___x_419_);
v___x_421_ = lean_box(v___x_420_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v___y_395_ = v___y_412_;
v___y_396_ = v___x_413_;
v___y_397_ = v___x_423_;
goto v___jp_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* v_prev_x3f_438_, lean_object* v_curr_439_, lean_object* v_next_x3f_440_){
_start:
{
uint32_t v_curr_boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v_curr_boxed_441_ = lean_unbox_uint32(v_curr_439_);
lean_dec(v_curr_439_);
v_res_442_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_438_, v_curr_boxed_441_, v_next_x3f_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* v_string_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_string_utf8_byte_size(v_string_446_);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_string_length(v_string_446_);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v_result_453_; lean_object* v___x_454_; uint32_t v___x_455_; uint32_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v_result_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint32_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint32_t v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_result_453_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_string_utf8_get(v_string_446_, v___x_448_);
v___x_456_ = lean_string_utf8_get(v_string_446_, v___x_451_);
v___x_457_ = lean_box_uint32(v___x_456_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___x_459_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_454_, v___x_455_, v___x_458_);
v___x_460_ = lean_box(v___x_459_);
v_result_461_ = lean_array_push(v_result_453_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(2u);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_450_);
lean_ctor_set(v___x_463_, 2, v___x_451_);
v___x_464_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_446_, v___x_463_, v_result_461_, v___x_462_);
lean_dec_ref(v___x_463_);
v___x_465_ = lean_nat_sub(v___x_450_, v___x_462_);
v___x_466_ = lean_string_utf8_get(v_string_446_, v___x_465_);
lean_dec(v___x_465_);
v___x_467_ = lean_box_uint32(v___x_466_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = lean_nat_sub(v___x_450_, v___x_451_);
v___x_470_ = lean_string_utf8_get(v_string_446_, v___x_469_);
lean_dec(v___x_469_);
v___x_471_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_468_, v___x_470_, v___x_454_);
v___x_472_ = lean_box(v___x_471_);
v___x_473_ = lean_array_push(v___x_464_, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; uint32_t v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_string_utf8_get(v_string_446_, v___x_448_);
v___x_476_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_474_, v___x_475_, v___x_474_);
v___x_477_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_478_ = lean_box(v___x_476_);
v___x_479_ = lean_array_push(v___x_477_, v___x_478_);
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0));
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* v_string_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_481_);
lean_dec_ref(v_string_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* v_s_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_485_);
lean_dec_ref(v_s_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* v_string_487_, lean_object* v_range_488_, lean_object* v_b_489_, lean_object* v_i_490_, lean_object* v_hs_491_, lean_object* v_hl_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_487_, v_range_488_, v_b_489_, v_i_490_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* v_string_494_, lean_object* v_range_495_, lean_object* v_b_496_, lean_object* v_i_497_, lean_object* v_hs_498_, lean_object* v_hl_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_494_, v_range_495_, v_b_496_, v_i_497_, v_hs_498_, v_hl_499_);
lean_dec(v_i_497_);
lean_dec_ref(v_range_495_);
lean_dec_ref(v_string_494_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* v_string_501_, lean_object* v_range_502_, lean_object* v_b_503_, lean_object* v_i_504_, lean_object* v_hs_505_, lean_object* v_hl_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_501_, v_range_502_, v_b_503_, v_i_504_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_string_508_, lean_object* v_range_509_, lean_object* v_b_510_, lean_object* v_i_511_, lean_object* v_hs_512_, lean_object* v_hl_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_508_, v_range_509_, v_b_510_, v_i_511_, v_hs_512_, v_hl_513_);
lean_dec_ref(v_range_509_);
lean_dec_ref(v_string_508_);
return v_res_514_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0(void){
_start:
{
lean_object* v___x_515_; uint16_t v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_int16_of_nat(v___x_515_);
return v___x_516_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default(void){
_start:
{
uint16_t v___x_517_; 
v___x_517_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_517_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore(void){
_start:
{
uint16_t v___x_518_; 
v___x_518_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
return v___x_518_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0(void){
_start:
{
lean_object* v___x_519_; uint16_t v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(32768u);
v___x_520_ = lean_int16_of_nat(v___x_519_);
return v___x_520_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1(void){
_start:
{
uint16_t v___x_521_; uint16_t v___x_522_; 
v___x_521_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0);
v___x_522_ = lean_int16_neg(v___x_521_);
return v___x_522_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful(void){
_start:
{
uint16_t v___x_523_; 
v___x_523_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
return v___x_523_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t v_x_524_){
_start:
{
uint16_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_526_ = lean_int16_dec_le(v_x_524_, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* v_x_527_){
_start:
{
uint16_t v_x_boxed_528_; uint8_t v_res_529_; lean_object* v_r_530_; 
v_x_boxed_528_ = lean_unbox(v_x_527_);
v_res_529_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t v_x_531_, lean_object* v_f_532_){
_start:
{
uint16_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_534_ = lean_int16_dec_le(v_x_531_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; uint16_t v___x_537_; 
v___x_535_ = lean_box(v_x_531_);
v___x_536_ = lean_apply_1(v_f_532_, v___x_535_);
v___x_537_ = lean_unbox(v___x_536_);
return v___x_537_;
}
else
{
lean_dec_ref(v_f_532_);
return v_x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* v_x_538_, lean_object* v_f_539_){
_start:
{
uint16_t v_x_boxed_540_; uint16_t v_res_541_; lean_object* v_r_542_; 
v_x_boxed_540_ = lean_unbox(v_x_538_);
v_res_541_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_boxed_540_, v_f_539_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t v_x_543_){
_start:
{
uint16_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_545_ = lean_int16_dec_le(v_x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_box(v_x_543_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(0);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* v_x_549_){
_start:
{
uint16_t v_x_boxed_550_; lean_object* v_res_551_; 
v_x_boxed_550_ = lean_unbox(v_x_549_);
v_res_551_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_boxed_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t v_x_552_){
_start:
{
uint16_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_554_ = lean_int16_dec_le(v_x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_int16_to_int(v_x_552_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_box(0);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* v_x_558_){
_start:
{
uint16_t v_x_boxed_559_; lean_object* v_res_560_; 
v_x_boxed_559_ = lean_unbox(v_x_558_);
v_res_560_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_559_);
return v_res_560_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_564_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
v___x_565_ = lean_unsigned_to_nat(2u);
v___x_566_ = lean_unsigned_to_nat(124u);
v___x_567_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
v___x_568_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
v___x_569_ = l_mkPanicMessageWithDecl(v___x_568_, v___x_567_, v___x_566_, v___x_565_, v___x_564_);
return v___x_569_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t v_x_570_){
_start:
{
uint16_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_572_ = lean_int16_dec_eq(v_x_570_, v___x_571_);
if (v___x_572_ == 0)
{
return v_x_570_;
}
else
{
uint16_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint16_t v___x_577_; 
v___x_573_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_574_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_575_ = lean_box(v___x_573_);
v___x_576_ = l_panic___redArg(v___x_575_, v___x_574_);
lean_dec(v___x_575_);
v___x_577_ = lean_unbox(v___x_576_);
lean_dec(v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* v_x_578_){
_start:
{
uint16_t v_x_boxed_579_; uint16_t v_res_580_; lean_object* v_r_581_; 
v_x_boxed_579_ = lean_unbox(v_x_578_);
v_res_580_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_boxed_579_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t v_missScore_582_, uint16_t v_matchScore_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_int16_dec_le(v_missScore_582_, v_matchScore_583_);
if (v___x_584_ == 0)
{
return v_missScore_582_;
}
else
{
return v_matchScore_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* v_missScore_585_, lean_object* v_matchScore_586_){
_start:
{
uint16_t v_missScore_boxed_587_; uint16_t v_matchScore_boxed_588_; uint16_t v_res_589_; lean_object* v_r_590_; 
v_missScore_boxed_587_ = lean_unbox(v_missScore_585_);
v_matchScore_boxed_588_ = lean_unbox(v_matchScore_586_);
v_res_589_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_boxed_587_, v_matchScore_boxed_588_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* v_word_591_, lean_object* v_patternIdx_592_, lean_object* v_wordIdx_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = lean_string_length(v_word_591_);
v___x_595_ = lean_nat_mul(v_patternIdx_592_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(2u);
v___x_597_ = lean_nat_mul(v___x_595_, v___x_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_nat_mul(v_wordIdx_593_, v___x_596_);
v___x_599_ = lean_nat_add(v___x_597_, v___x_598_);
lean_dec(v___x_598_);
lean_dec(v___x_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* v_word_600_, lean_object* v_patternIdx_601_, lean_object* v_wordIdx_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(v_word_600_, v_patternIdx_601_, v_wordIdx_602_);
lean_dec(v_wordIdx_602_);
lean_dec(v_patternIdx_601_);
lean_dec_ref(v_word_600_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* v_word_604_, lean_object* v_patternIdx_605_, lean_object* v_wordIdx_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_string_length(v_word_604_);
v___x_608_ = lean_nat_mul(v_patternIdx_605_, v___x_607_);
v___x_609_ = lean_nat_add(v___x_608_, v_wordIdx_606_);
lean_dec(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* v_word_610_, lean_object* v_patternIdx_611_, lean_object* v_wordIdx_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(v_word_610_, v_patternIdx_611_, v_wordIdx_612_);
lean_dec(v_wordIdx_612_);
lean_dec(v_patternIdx_611_);
lean_dec_ref(v_word_610_);
return v_res_613_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* v_word_614_, lean_object* v_result_615_, lean_object* v_patternIdx_616_, lean_object* v_wordIdx_617_){
_start:
{
uint16_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint16_t v___x_627_; 
v___x_618_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_619_ = lean_string_length(v_word_614_);
v___x_620_ = lean_nat_mul(v_patternIdx_616_, v___x_619_);
v___x_621_ = lean_unsigned_to_nat(2u);
v___x_622_ = lean_nat_mul(v___x_620_, v___x_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_nat_mul(v_wordIdx_617_, v___x_621_);
v___x_624_ = lean_nat_add(v___x_622_, v___x_623_);
lean_dec(v___x_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(v___x_618_);
v___x_626_ = lean_array_get(v___x_625_, v_result_615_, v___x_624_);
lean_dec(v___x_624_);
lean_dec(v___x_625_);
v___x_627_ = lean_unbox(v___x_626_);
lean_dec(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* v_word_628_, lean_object* v_result_629_, lean_object* v_patternIdx_630_, lean_object* v_wordIdx_631_){
_start:
{
uint16_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_628_, v_result_629_, v_patternIdx_630_, v_wordIdx_631_);
lean_dec(v_wordIdx_631_);
lean_dec(v_patternIdx_630_);
lean_dec_ref(v_result_629_);
lean_dec_ref(v_word_628_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* v_word_634_, lean_object* v_result_635_, lean_object* v_patternIdx_636_, lean_object* v_wordIdx_637_){
_start:
{
uint16_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint16_t v___x_649_; 
v___x_638_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_639_ = lean_string_length(v_word_634_);
v___x_640_ = lean_nat_mul(v_patternIdx_636_, v___x_639_);
v___x_641_ = lean_unsigned_to_nat(2u);
v___x_642_ = lean_nat_mul(v___x_640_, v___x_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_nat_mul(v_wordIdx_637_, v___x_641_);
v___x_644_ = lean_nat_add(v___x_642_, v___x_643_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v___x_644_, v___x_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(v___x_638_);
v___x_648_ = lean_array_get(v___x_647_, v_result_635_, v___x_646_);
lean_dec(v___x_646_);
lean_dec(v___x_647_);
v___x_649_ = lean_unbox(v___x_648_);
lean_dec(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* v_word_650_, lean_object* v_result_651_, lean_object* v_patternIdx_652_, lean_object* v_wordIdx_653_){
_start:
{
uint16_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_650_, v_result_651_, v_patternIdx_652_, v_wordIdx_653_);
lean_dec(v_wordIdx_653_);
lean_dec(v_patternIdx_652_);
lean_dec_ref(v_result_651_);
lean_dec_ref(v_word_650_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* v_word_656_, lean_object* v_result_657_, lean_object* v_patternIdx_658_, lean_object* v_wordIdx_659_, uint16_t v_missValue_660_, uint16_t v_matchValue_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_idx_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_662_ = lean_string_length(v_word_656_);
v___x_663_ = lean_nat_mul(v_patternIdx_658_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(2u);
v___x_665_ = lean_nat_mul(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_nat_mul(v_wordIdx_659_, v___x_664_);
v_idx_667_ = lean_nat_add(v___x_665_, v___x_666_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(v_missValue_660_);
v___x_669_ = lean_array_set(v_result_657_, v_idx_667_, v___x_668_);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_idx_667_, v___x_670_);
lean_dec(v_idx_667_);
v___x_672_ = lean_box(v_matchValue_661_);
v___x_673_ = lean_array_set(v___x_669_, v___x_671_, v___x_672_);
lean_dec(v___x_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* v_word_674_, lean_object* v_result_675_, lean_object* v_patternIdx_676_, lean_object* v_wordIdx_677_, lean_object* v_missValue_678_, lean_object* v_matchValue_679_){
_start:
{
uint16_t v_missValue_boxed_680_; uint16_t v_matchValue_boxed_681_; lean_object* v_res_682_; 
v_missValue_boxed_680_ = lean_unbox(v_missValue_678_);
v_matchValue_boxed_681_ = lean_unbox(v_matchValue_679_);
v_res_682_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_674_, v_result_675_, v_patternIdx_676_, v_wordIdx_677_, v_missValue_boxed_680_, v_matchValue_boxed_681_);
lean_dec(v_wordIdx_677_);
lean_dec(v_patternIdx_676_);
lean_dec_ref(v_word_674_);
return v_res_682_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0(void){
_start:
{
lean_object* v___x_683_; uint16_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_int16_of_nat(v___x_683_);
return v___x_684_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1(void){
_start:
{
lean_object* v___x_685_; uint16_t v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(3u);
v___x_686_ = lean_int16_of_nat(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t v_wordRole_687_, uint8_t v_wordStart_688_){
_start:
{
if (v_wordStart_688_ == 0)
{
if (v_wordRole_687_ == 0)
{
uint16_t v___x_689_; 
v___x_689_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
return v___x_689_;
}
else
{
uint16_t v___x_690_; 
v___x_690_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_690_;
}
}
else
{
uint16_t v___x_691_; 
v___x_691_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* v_wordRole_692_, lean_object* v_wordStart_693_){
_start:
{
uint8_t v_wordRole_boxed_694_; uint8_t v_wordStart_boxed_695_; uint16_t v_res_696_; lean_object* v_r_697_; 
v_wordRole_boxed_694_ = lean_unbox(v_wordRole_692_);
v_wordStart_boxed_695_ = lean_unbox(v_wordStart_693_);
v_res_696_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_boxed_694_, v_wordStart_boxed_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t v_patternChar_698_, uint32_t v_wordChar_699_, uint8_t v_patternRole_700_, uint8_t v_wordRole_701_){
_start:
{
uint32_t v___y_703_; uint32_t v___y_704_; uint32_t v___y_708_; uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 65;
v___x_716_ = lean_uint32_dec_le(v___x_715_, v_patternChar_698_);
if (v___x_716_ == 0)
{
v___y_708_ = v_patternChar_698_;
goto v___jp_707_;
}
else
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 90;
v___x_718_ = lean_uint32_dec_le(v_patternChar_698_, v___x_717_);
if (v___x_718_ == 0)
{
v___y_708_ = v_patternChar_698_;
goto v___jp_707_;
}
else
{
uint32_t v___x_719_; uint32_t v___x_720_; 
v___x_719_ = 32;
v___x_720_ = lean_uint32_add(v_patternChar_698_, v___x_719_);
v___y_708_ = v___x_720_;
goto v___jp_707_;
}
}
v___jp_702_:
{
uint8_t v___x_705_; 
v___x_705_ = lean_uint32_dec_eq(v___y_703_, v___y_704_);
if (v___x_705_ == 0)
{
return v___x_705_;
}
else
{
if (v_patternRole_700_ == 0)
{
if (v_wordRole_701_ == 0)
{
return v___x_705_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = 0;
return v___x_706_;
}
}
else
{
return v___x_705_;
}
}
}
v___jp_707_:
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 65;
v___x_710_ = lean_uint32_dec_le(v___x_709_, v_wordChar_699_);
if (v___x_710_ == 0)
{
v___y_703_ = v___y_708_;
v___y_704_ = v_wordChar_699_;
goto v___jp_702_;
}
else
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 90;
v___x_712_ = lean_uint32_dec_le(v_wordChar_699_, v___x_711_);
if (v___x_712_ == 0)
{
v___y_703_ = v___y_708_;
v___y_704_ = v_wordChar_699_;
goto v___jp_702_;
}
else
{
uint32_t v___x_713_; uint32_t v___x_714_; 
v___x_713_ = 32;
v___x_714_ = lean_uint32_add(v_wordChar_699_, v___x_713_);
v___y_703_ = v___y_708_;
v___y_704_ = v___x_714_;
goto v___jp_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object* v_patternChar_721_, lean_object* v_wordChar_722_, lean_object* v_patternRole_723_, lean_object* v_wordRole_724_){
_start:
{
uint32_t v_patternChar_boxed_725_; uint32_t v_wordChar_boxed_726_; uint8_t v_patternRole_boxed_727_; uint8_t v_wordRole_boxed_728_; uint8_t v_res_729_; lean_object* v_r_730_; 
v_patternChar_boxed_725_ = lean_unbox_uint32(v_patternChar_721_);
lean_dec(v_patternChar_721_);
v_wordChar_boxed_726_ = lean_unbox_uint32(v_wordChar_722_);
lean_dec(v_wordChar_722_);
v_patternRole_boxed_727_ = lean_unbox(v_patternRole_723_);
v_wordRole_boxed_728_ = lean_unbox(v_wordRole_724_);
v_res_729_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v_patternChar_boxed_725_, v_wordChar_boxed_726_, v_patternRole_boxed_727_, v_wordRole_boxed_728_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0(void){
_start:
{
lean_object* v___x_731_; uint16_t v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_int16_of_nat(v___x_731_);
return v___x_732_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1(void){
_start:
{
uint16_t v_score_733_; uint16_t v_score_734_; 
v_score_733_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v_score_734_ = lean_int16_add(v_score_733_, v_score_733_);
return v_score_734_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object* v_pattern_735_, lean_object* v_word_736_, lean_object* v_patternIdx_737_, lean_object* v_wordIdx_738_, uint8_t v_patternRole_739_, uint8_t v_wordRole_740_, uint16_t v_consecutive_741_){
_start:
{
uint16_t v_score_743_; uint16_t v_score_748_; uint16_t v___y_754_; uint8_t v___y_755_; lean_object* v___x_758_; uint16_t v_score_760_; uint16_t v_score_767_; uint8_t v___y_771_; uint32_t v___x_772_; uint32_t v___x_773_; uint8_t v___x_774_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v_score_767_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_772_ = lean_string_utf8_get(v_pattern_735_, v_patternIdx_737_);
v___x_773_ = lean_string_utf8_get(v_word_736_, v_wordIdx_738_);
v___x_774_ = lean_uint32_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
if (v_patternRole_739_ == 0)
{
if (v_wordRole_740_ == 0)
{
goto v___jp_768_;
}
else
{
v___y_771_ = v___x_774_;
goto v___jp_770_;
}
}
else
{
v___y_771_ = v___x_774_;
goto v___jp_770_;
}
}
else
{
v___y_771_ = v___x_774_;
goto v___jp_770_;
}
v___jp_742_:
{
uint16_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_745_ = lean_int16_dec_le(v_consecutive_741_, v___x_744_);
if (v___x_745_ == 0)
{
uint16_t v___x_746_; 
v___x_746_ = lean_int16_add(v_score_743_, v_consecutive_741_);
return v___x_746_;
}
else
{
return v_score_743_;
}
}
v___jp_747_:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_nat_dec_eq(v_wordIdx_738_, v___x_749_);
if (v___x_750_ == 0)
{
v_score_743_ = v_score_748_;
goto v___jp_742_;
}
else
{
uint16_t v___x_751_; uint16_t v_score_752_; 
v___x_751_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
v_score_752_ = lean_int16_add(v_score_748_, v___x_751_);
v_score_743_ = v_score_752_;
goto v___jp_742_;
}
}
v___jp_753_:
{
if (v___y_755_ == 0)
{
v_score_748_ = v___y_754_;
goto v___jp_747_;
}
else
{
uint16_t v___x_756_; uint16_t v_score_757_; 
v___x_756_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
v_score_757_ = lean_int16_add(v___y_754_, v___x_756_);
v_score_748_ = v_score_757_;
goto v___jp_747_;
}
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_string_length(v_word_736_);
v___x_762_ = lean_nat_sub(v___x_761_, v___x_758_);
v___x_763_ = lean_nat_dec_eq(v_wordIdx_738_, v___x_762_);
lean_dec(v___x_762_);
if (v___x_763_ == 0)
{
v___y_754_ = v_score_760_;
v___y_755_ = v___x_763_;
goto v___jp_753_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_764_ = lean_string_length(v_pattern_735_);
v___x_765_ = lean_nat_sub(v___x_764_, v___x_758_);
v___x_766_ = lean_nat_dec_eq(v_patternIdx_737_, v___x_765_);
lean_dec(v___x_765_);
v___y_754_ = v_score_760_;
v___y_755_ = v___x_766_;
goto v___jp_753_;
}
}
v___jp_768_:
{
uint16_t v_score_769_; 
v_score_769_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
v_score_760_ = v_score_769_;
goto v___jp_759_;
}
v___jp_770_:
{
if (v___y_771_ == 0)
{
v_score_760_ = v_score_767_;
goto v___jp_759_;
}
else
{
goto v___jp_768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* v_pattern_775_, lean_object* v_word_776_, lean_object* v_patternIdx_777_, lean_object* v_wordIdx_778_, lean_object* v_patternRole_779_, lean_object* v_wordRole_780_, lean_object* v_consecutive_781_){
_start:
{
uint8_t v_patternRole_boxed_782_; uint8_t v_wordRole_boxed_783_; uint16_t v_consecutive_boxed_784_; uint16_t v_res_785_; lean_object* v_r_786_; 
v_patternRole_boxed_782_ = lean_unbox(v_patternRole_779_);
v_wordRole_boxed_783_ = lean_unbox(v_wordRole_780_);
v_consecutive_boxed_784_ = lean_unbox(v_consecutive_781_);
v_res_785_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_775_, v_word_776_, v_patternIdx_777_, v_wordIdx_778_, v_patternRole_boxed_782_, v_wordRole_boxed_783_, v_consecutive_boxed_784_);
lean_dec(v_wordIdx_778_);
lean_dec(v_patternIdx_777_);
lean_dec_ref(v_word_776_);
lean_dec_ref(v_pattern_775_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* v_msg_787_){
_start:
{
uint16_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint16_t v___x_791_; 
v___x_788_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_789_ = lean_box(v___x_788_);
v___x_790_ = lean_panic_fn_borrowed(v___x_789_, v_msg_787_);
lean_dec(v___x_789_);
v___x_791_ = lean_unbox(v___x_790_);
lean_dec(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* v_msg_792_){
_start:
{
uint16_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* v___x_795_, lean_object* v_a_796_, uint16_t v_x_797_){
_start:
{
uint16_t v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_799_ = lean_int16_dec_le(v_x_797_, v___x_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; 
v___x_800_ = lean_nat_dec_le(v___x_795_, v_a_796_);
if (v___x_800_ == 0)
{
return v_x_797_;
}
else
{
uint16_t v___x_801_; uint16_t v___x_802_; 
v___x_801_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_802_ = lean_int16_add(v_x_797_, v___x_801_);
return v___x_802_;
}
}
else
{
return v_x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* v___x_803_, lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
uint16_t v_x_boxed_806_; uint16_t v_res_807_; lean_object* v_r_808_; 
v_x_boxed_806_ = lean_unbox(v_x_805_);
v_res_807_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_803_, v_a_804_, v_x_boxed_806_);
lean_dec(v_a_804_);
lean_dec(v___x_803_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* v_pattern_809_, lean_object* v_word_810_, lean_object* v_a_811_, lean_object* v_a_812_, uint8_t v___x_813_, uint8_t v___x_814_, lean_object* v___x_815_, uint16_t v_x_816_){
_start:
{
uint16_t v_matchScore_817_; uint8_t v___x_818_; 
v_matchScore_817_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_818_ = lean_int16_dec_le(v_x_816_, v_matchScore_817_);
if (v___x_818_ == 0)
{
uint16_t v___x_819_; uint16_t v___x_820_; uint16_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint16_t v___x_824_; uint16_t v___x_825_; 
v___x_819_ = l_instInhabitedInt16;
v___x_820_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_809_, v_word_810_, v_a_811_, v_a_812_, v___x_813_, v___x_814_, v_matchScore_817_);
v___x_821_ = lean_int16_add(v_x_816_, v___x_820_);
v___x_822_ = lean_box(v___x_819_);
v___x_823_ = lean_array_get(v___x_822_, v___x_815_, v_a_812_);
lean_dec(v___x_822_);
v___x_824_ = lean_unbox(v___x_823_);
lean_dec(v___x_823_);
v___x_825_ = lean_int16_sub(v___x_821_, v___x_824_);
return v___x_825_;
}
else
{
return v_x_816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* v_pattern_826_, lean_object* v_word_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v___x_832_, lean_object* v_x_833_){
_start:
{
uint8_t v___x_3252__boxed_834_; uint8_t v___x_3253__boxed_835_; uint16_t v_x_boxed_836_; uint16_t v_res_837_; lean_object* v_r_838_; 
v___x_3252__boxed_834_ = lean_unbox(v___x_830_);
v___x_3253__boxed_835_ = lean_unbox(v___x_831_);
v_x_boxed_836_ = lean_unbox(v_x_833_);
v_res_837_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_826_, v_word_827_, v_a_828_, v_a_829_, v___x_3252__boxed_834_, v___x_3253__boxed_835_, v___x_832_, v_x_boxed_836_);
lean_dec_ref(v___x_832_);
lean_dec(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_word_827_);
lean_dec_ref(v_pattern_826_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* v_pattern_839_, lean_object* v_word_840_, lean_object* v_a_841_, lean_object* v_a_842_, uint8_t v___x_843_, uint8_t v___x_844_, uint16_t v___x_845_, uint16_t v_x_846_){
_start:
{
uint16_t v___y_848_; uint16_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_852_ = lean_int16_dec_le(v_x_846_, v___x_851_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; 
v___x_853_ = lean_int16_dec_eq(v___x_845_, v___x_851_);
if (v___x_853_ == 0)
{
v___y_848_ = v___x_845_;
goto v___jp_847_;
}
else
{
lean_object* v___x_854_; uint16_t v___x_855_; 
v___x_854_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_855_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_854_);
v___y_848_ = v___x_855_;
goto v___jp_847_;
}
}
else
{
return v_x_846_;
}
v___jp_847_:
{
uint16_t v___x_849_; uint16_t v___x_850_; 
v___x_849_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_839_, v_word_840_, v_a_841_, v_a_842_, v___x_843_, v___x_844_, v___y_848_);
v___x_850_ = lean_int16_add(v_x_846_, v___x_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* v_pattern_856_, lean_object* v_word_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v_x_863_){
_start:
{
uint8_t v___x_3292__boxed_864_; uint8_t v___x_3293__boxed_865_; uint16_t v___x_3294__boxed_866_; uint16_t v_x_boxed_867_; uint16_t v_res_868_; lean_object* v_r_869_; 
v___x_3292__boxed_864_ = lean_unbox(v___x_860_);
v___x_3293__boxed_865_ = lean_unbox(v___x_861_);
v___x_3294__boxed_866_ = lean_unbox(v___x_862_);
v_x_boxed_867_ = lean_unbox(v_x_863_);
v_res_868_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_856_, v_word_857_, v_a_858_, v_a_859_, v___x_3292__boxed_864_, v___x_3293__boxed_865_, v___x_3294__boxed_866_, v_x_boxed_867_);
lean_dec(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_word_857_);
lean_dec_ref(v_pattern_856_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* v_word_870_, lean_object* v_a_871_, lean_object* v_pattern_872_, lean_object* v_patternRoles_873_, lean_object* v_wordRoles_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v_range_877_, lean_object* v_b_878_, lean_object* v_i_879_){
_start:
{
lean_object* v_stop_880_; lean_object* v_step_881_; uint8_t v___x_882_; 
v_stop_880_ = lean_ctor_get(v_range_877_, 1);
v_step_881_ = lean_ctor_get(v_range_877_, 2);
v___x_882_ = lean_nat_dec_lt(v_i_879_, v_stop_880_);
if (v___x_882_ == 0)
{
lean_dec(v_i_879_);
return v_b_878_;
}
else
{
lean_object* v_fst_883_; lean_object* v_snd_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_998_; 
v_fst_883_ = lean_ctor_get(v_b_878_, 0);
v_snd_884_ = lean_ctor_get(v_b_878_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_b_878_);
if (v_isSharedCheck_998_ == 0)
{
v___x_886_ = v_b_878_;
v_isShared_887_ = v_isSharedCheck_998_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_snd_884_);
lean_inc(v_fst_883_);
lean_dec(v_b_878_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_998_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
uint8_t v___x_888_; uint16_t v_matchScore_889_; lean_object* v___x_890_; uint16_t v___y_892_; lean_object* v_runLengths_893_; uint16_t v_matchScore_894_; lean_object* v___y_912_; uint16_t v___y_913_; uint16_t v___y_914_; uint16_t v___y_917_; uint8_t v___x_979_; 
v___x_888_ = 0;
v_matchScore_889_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_979_ = lean_nat_dec_le(v___x_890_, v_i_879_);
if (v___x_979_ == 0)
{
v___y_917_ = v_matchScore_889_;
goto v___jp_916_;
}
else
{
lean_object* v___x_980_; uint16_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint16_t v___x_993_; uint16_t v___x_994_; uint8_t v___x_995_; 
v___x_980_ = lean_nat_sub(v_i_879_, v___x_890_);
v___x_981_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_982_ = lean_string_length(v_word_870_);
v___x_983_ = lean_nat_mul(v_a_871_, v___x_982_);
v___x_984_ = lean_unsigned_to_nat(2u);
v___x_985_ = lean_nat_mul(v___x_983_, v___x_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_nat_mul(v___x_980_, v___x_984_);
lean_dec(v___x_980_);
v___x_987_ = lean_nat_add(v___x_985_, v___x_986_);
lean_dec(v___x_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(v___x_981_);
v___x_989_ = lean_array_get(v___x_988_, v_fst_883_, v___x_987_);
lean_dec(v___x_988_);
v___x_990_ = lean_nat_add(v___x_987_, v___x_890_);
lean_dec(v___x_987_);
v___x_991_ = lean_box(v___x_981_);
v___x_992_ = lean_array_get(v___x_991_, v_fst_883_, v___x_990_);
lean_dec(v___x_990_);
lean_dec(v___x_991_);
v___x_993_ = lean_unbox(v___x_989_);
v___x_994_ = lean_unbox(v___x_992_);
v___x_995_ = lean_int16_dec_le(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
uint16_t v___x_996_; 
lean_dec(v___x_992_);
v___x_996_ = lean_unbox(v___x_989_);
lean_dec(v___x_989_);
v___y_917_ = v___x_996_;
goto v___jp_916_;
}
else
{
uint16_t v___x_997_; 
lean_dec(v___x_989_);
v___x_997_ = lean_unbox(v___x_992_);
lean_dec(v___x_992_);
v___y_917_ = v___x_997_;
goto v___jp_916_;
}
}
v___jp_891_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_idx_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_895_ = lean_string_length(v_word_870_);
v___x_896_ = lean_nat_mul(v_a_871_, v___x_895_);
v___x_897_ = lean_unsigned_to_nat(2u);
v___x_898_ = lean_nat_mul(v___x_896_, v___x_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_nat_mul(v_i_879_, v___x_897_);
v_idx_900_ = lean_nat_add(v___x_898_, v___x_899_);
lean_dec(v___x_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(v___y_892_);
v___x_902_ = lean_array_set(v_fst_883_, v_idx_900_, v___x_901_);
v___x_903_ = lean_nat_add(v_idx_900_, v___x_890_);
lean_dec(v_idx_900_);
v___x_904_ = lean_box(v_matchScore_894_);
v___x_905_ = lean_array_set(v___x_902_, v___x_903_, v___x_904_);
lean_dec(v___x_903_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v_runLengths_893_);
lean_ctor_set(v___x_886_, 0, v___x_905_);
v___x_907_ = v___x_886_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_runLengths_893_);
v___x_907_ = v_reuseFailAlloc_910_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = lean_nat_add(v_i_879_, v_step_881_);
lean_dec(v_i_879_);
v_b_878_ = v___x_907_;
v_i_879_ = v___x_908_;
goto _start;
}
}
v___jp_911_:
{
uint16_t v___x_915_; 
v___x_915_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_876_, v_i_879_, v___y_914_);
v___y_892_ = v___y_913_;
v_runLengths_893_ = v___y_912_;
v_matchScore_894_ = v___x_915_;
goto v___jp_891_;
}
v___jp_916_:
{
uint32_t v___x_918_; uint32_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; uint8_t v___x_925_; uint8_t v___x_926_; 
v___x_918_ = lean_string_utf8_get(v_pattern_872_, v_a_871_);
v___x_919_ = lean_string_utf8_get(v_word_870_, v_i_879_);
v___x_920_ = lean_box(v___x_888_);
v___x_921_ = lean_array_get(v___x_920_, v_patternRoles_873_, v_a_871_);
lean_dec(v___x_920_);
v___x_922_ = lean_box(v___x_888_);
v___x_923_ = lean_array_get(v___x_922_, v_wordRoles_874_, v_i_879_);
lean_dec(v___x_922_);
v___x_924_ = lean_unbox(v___x_921_);
v___x_925_ = lean_unbox(v___x_923_);
v___x_926_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_918_, v___x_919_, v___x_924_, v___x_925_);
if (v___x_926_ == 0)
{
lean_dec(v___x_923_);
lean_dec(v___x_921_);
v___y_892_ = v___y_917_;
v_runLengths_893_ = v_snd_884_;
v_matchScore_894_ = v_matchScore_889_;
goto v___jp_891_;
}
else
{
uint8_t v___x_927_; 
v___x_927_ = lean_nat_dec_le(v___x_890_, v_a_871_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint16_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; uint8_t v___x_935_; uint16_t v___x_936_; uint16_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint16_t v___x_940_; uint16_t v___x_941_; uint8_t v___x_942_; 
v___x_928_ = lean_string_length(v_word_870_);
v___x_929_ = lean_nat_mul(v_a_871_, v___x_928_);
v___x_930_ = lean_nat_add(v___x_929_, v_i_879_);
lean_dec(v___x_929_);
v___x_931_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_932_ = lean_box(v___x_931_);
v___x_933_ = lean_array_set(v_snd_884_, v___x_930_, v___x_932_);
lean_dec(v___x_930_);
v___x_934_ = lean_unbox(v___x_921_);
lean_dec(v___x_921_);
v___x_935_ = lean_unbox(v___x_923_);
lean_dec(v___x_923_);
v___x_936_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_872_, v_word_870_, v_a_871_, v_i_879_, v___x_934_, v___x_935_, v_matchScore_889_);
v___x_937_ = l_instInhabitedInt16;
v___x_938_ = lean_box(v___x_937_);
v___x_939_ = lean_array_get(v___x_938_, v___x_875_, v_i_879_);
lean_dec(v___x_938_);
v___x_940_ = lean_unbox(v___x_939_);
lean_dec(v___x_939_);
v___x_941_ = lean_int16_sub(v___x_936_, v___x_940_);
v___x_942_ = lean_int16_dec_eq(v___x_941_, v_matchScore_889_);
if (v___x_942_ == 0)
{
v___y_892_ = v___y_917_;
v_runLengths_893_ = v___x_933_;
v_matchScore_894_ = v___x_941_;
goto v___jp_891_;
}
else
{
lean_object* v___x_943_; uint16_t v___x_944_; 
v___x_943_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_944_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_943_);
v___y_892_ = v___y_917_;
v_runLengths_893_ = v___x_933_;
v_matchScore_894_ = v___x_944_;
goto v___jp_891_;
}
}
else
{
uint16_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint16_t v___x_953_; uint16_t v___x_954_; uint16_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint16_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; uint16_t v___x_969_; uint16_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; uint16_t v___x_976_; uint16_t v___x_977_; uint8_t v___x_978_; 
v___x_945_ = l_instInhabitedInt16;
v___x_946_ = lean_nat_sub(v_a_871_, v___x_890_);
v___x_947_ = lean_nat_sub(v_i_879_, v___x_890_);
v___x_948_ = lean_string_length(v_word_870_);
v___x_949_ = lean_nat_mul(v___x_946_, v___x_948_);
lean_dec(v___x_946_);
v___x_950_ = lean_nat_add(v___x_949_, v___x_947_);
v___x_951_ = lean_box(v___x_945_);
v___x_952_ = lean_array_get(v___x_951_, v_snd_884_, v___x_950_);
lean_dec(v___x_950_);
lean_dec(v___x_951_);
v___x_953_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_954_ = lean_unbox(v___x_952_);
lean_dec(v___x_952_);
v___x_955_ = lean_int16_add(v___x_954_, v___x_953_);
v___x_956_ = lean_nat_mul(v_a_871_, v___x_948_);
v___x_957_ = lean_nat_add(v___x_956_, v_i_879_);
lean_dec(v___x_956_);
v___x_958_ = lean_box(v___x_955_);
v___x_959_ = lean_array_set(v_snd_884_, v___x_957_, v___x_958_);
lean_dec(v___x_957_);
v___x_960_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_961_ = lean_unsigned_to_nat(2u);
v___x_962_ = lean_nat_mul(v___x_949_, v___x_961_);
lean_dec(v___x_949_);
v___x_963_ = lean_nat_mul(v___x_947_, v___x_961_);
lean_dec(v___x_947_);
v___x_964_ = lean_nat_add(v___x_962_, v___x_963_);
lean_dec(v___x_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(v___x_960_);
v___x_966_ = lean_array_get(v___x_965_, v_fst_883_, v___x_964_);
lean_dec(v___x_965_);
v___x_967_ = lean_unbox(v___x_921_);
v___x_968_ = lean_unbox(v___x_923_);
v___x_969_ = lean_unbox(v___x_966_);
lean_dec(v___x_966_);
v___x_970_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_872_, v_word_870_, v_a_871_, v_i_879_, v___x_967_, v___x_968_, v___x_875_, v___x_969_);
v___x_971_ = lean_nat_add(v___x_964_, v___x_890_);
lean_dec(v___x_964_);
v___x_972_ = lean_box(v___x_960_);
v___x_973_ = lean_array_get(v___x_972_, v_fst_883_, v___x_971_);
lean_dec(v___x_971_);
lean_dec(v___x_972_);
v___x_974_ = lean_unbox(v___x_921_);
lean_dec(v___x_921_);
v___x_975_ = lean_unbox(v___x_923_);
lean_dec(v___x_923_);
v___x_976_ = lean_unbox(v___x_973_);
lean_dec(v___x_973_);
v___x_977_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_872_, v_word_870_, v_a_871_, v_i_879_, v___x_974_, v___x_975_, v___x_955_, v___x_976_);
v___x_978_ = lean_int16_dec_le(v___x_970_, v___x_977_);
if (v___x_978_ == 0)
{
v___y_912_ = v___x_959_;
v___y_913_ = v___y_917_;
v___y_914_ = v___x_970_;
goto v___jp_911_;
}
else
{
v___y_912_ = v___x_959_;
v___y_913_ = v___y_917_;
v___y_914_ = v___x_977_;
goto v___jp_911_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* v_word_999_, lean_object* v_a_1000_, lean_object* v_pattern_1001_, lean_object* v_patternRoles_1002_, lean_object* v_wordRoles_1003_, lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v_range_1006_, lean_object* v_b_1007_, lean_object* v_i_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_999_, v_a_1000_, v_pattern_1001_, v_patternRoles_1002_, v_wordRoles_1003_, v___x_1004_, v___x_1005_, v_range_1006_, v_b_1007_, v_i_1008_);
lean_dec_ref(v_range_1006_);
lean_dec(v___x_1005_);
lean_dec_ref(v___x_1004_);
lean_dec_ref(v_wordRoles_1003_);
lean_dec_ref(v_patternRoles_1002_);
lean_dec_ref(v_pattern_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_word_999_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_word_1012_, lean_object* v_pattern_1013_, lean_object* v_patternRoles_1014_, lean_object* v_wordRoles_1015_, lean_object* v___x_1016_, lean_object* v___x_1017_, lean_object* v_range_1018_, lean_object* v_b_1019_, lean_object* v_i_1020_){
_start:
{
lean_object* v_stop_1021_; lean_object* v_step_1022_; uint8_t v___x_1023_; 
v_stop_1021_ = lean_ctor_get(v_range_1018_, 1);
v_step_1022_ = lean_ctor_get(v_range_1018_, 2);
v___x_1023_ = lean_nat_dec_lt(v_i_1020_, v_stop_1021_);
if (v___x_1023_ == 0)
{
lean_dec(v_i_1020_);
return v_b_1019_;
}
else
{
lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1049_; 
v_fst_1024_ = lean_ctor_get(v_b_1019_, 0);
v_snd_1025_ = lean_ctor_get(v_b_1019_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_b_1019_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1027_ = v_b_1019_;
v_isShared_1028_ = v_isSharedCheck_1049_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snd_1025_);
lean_inc(v_fst_1024_);
lean_dec(v_b_1019_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1049_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_sub(v___x_1010_, v_i_1020_);
v___x_1031_ = lean_nat_sub(v___x_1030_, v___x_1029_);
lean_dec(v___x_1030_);
v___x_1032_ = lean_nat_sub(v___x_1011_, v___x_1031_);
lean_dec(v___x_1031_);
lean_inc(v_i_1020_);
v___x_1033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1033_, 0, v_i_1020_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_ctor_set(v___x_1033_, 2, v___x_1029_);
if (v_isShared_1028_ == 0)
{
v___x_1035_ = v___x_1027_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_fst_1024_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_snd_1025_);
v___x_1035_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
lean_inc(v_i_1020_);
v___x_1036_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1012_, v_i_1020_, v_pattern_1013_, v_patternRoles_1014_, v_wordRoles_1015_, v___x_1016_, v___x_1017_, v___x_1033_, v___x_1035_, v_i_1020_);
lean_dec_ref(v___x_1033_);
v_fst_1037_ = lean_ctor_get(v___x_1036_, 0);
v_snd_1038_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_fst_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1038_);
v___x_1043_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_nat_add(v_i_1020_, v_step_1022_);
lean_dec(v_i_1020_);
v_b_1019_ = v___x_1043_;
v_i_1020_ = v___x_1044_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v_word_1052_, lean_object* v_pattern_1053_, lean_object* v_patternRoles_1054_, lean_object* v_wordRoles_1055_, lean_object* v___x_1056_, lean_object* v___x_1057_, lean_object* v_range_1058_, lean_object* v_b_1059_, lean_object* v_i_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1050_, v___x_1051_, v_word_1052_, v_pattern_1053_, v_patternRoles_1054_, v_wordRoles_1055_, v___x_1056_, v___x_1057_, v_range_1058_, v_b_1059_, v_i_1060_);
lean_dec_ref(v_range_1058_);
lean_dec(v___x_1057_);
lean_dec_ref(v___x_1056_);
lean_dec_ref(v_wordRoles_1055_);
lean_dec_ref(v_patternRoles_1054_);
lean_dec_ref(v_pattern_1053_);
lean_dec_ref(v_word_1052_);
lean_dec(v___x_1051_);
lean_dec(v___x_1050_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* v_word_1062_, lean_object* v_pattern_1063_, lean_object* v_patternRoles_1064_, lean_object* v_wordRoles_1065_, lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v_range_1070_, lean_object* v_b_1071_, lean_object* v_i_1072_){
_start:
{
lean_object* v_stop_1073_; lean_object* v_step_1074_; uint8_t v___x_1075_; 
v_stop_1073_ = lean_ctor_get(v_range_1070_, 1);
v_step_1074_ = lean_ctor_get(v_range_1070_, 2);
v___x_1075_ = lean_nat_dec_lt(v_i_1072_, v_stop_1073_);
if (v___x_1075_ == 0)
{
lean_dec(v_i_1072_);
return v_b_1071_;
}
else
{
lean_object* v_fst_1076_; lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1101_; 
v_fst_1076_ = lean_ctor_get(v_b_1071_, 0);
v_snd_1077_ = lean_ctor_get(v_b_1071_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_b_1071_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1079_ = v_b_1071_;
v_isShared_1080_ = v_isSharedCheck_1101_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_inc(v_fst_1076_);
lean_dec(v_b_1071_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1101_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_nat_sub(v___x_1068_, v_i_1072_);
v___x_1083_ = lean_nat_sub(v___x_1082_, v___x_1081_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_nat_sub(v___x_1069_, v___x_1083_);
lean_dec(v___x_1083_);
lean_inc(v_i_1072_);
v___x_1085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1085_, 0, v_i_1072_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
lean_ctor_set(v___x_1085_, 2, v___x_1081_);
if (v_isShared_1080_ == 0)
{
v___x_1087_ = v___x_1079_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_fst_1076_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_snd_1077_);
v___x_1087_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
lean_inc(v_i_1072_);
v___x_1088_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1062_, v_i_1072_, v_pattern_1063_, v_patternRoles_1064_, v_wordRoles_1065_, v___x_1066_, v___x_1067_, v___x_1085_, v___x_1087_, v_i_1072_);
lean_dec_ref(v___x_1085_);
v_fst_1089_ = lean_ctor_get(v___x_1088_, 0);
v_snd_1090_ = lean_ctor_get(v___x_1088_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1092_ = v___x_1088_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_snd_1090_);
lean_inc(v_fst_1089_);
lean_dec(v___x_1088_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1089_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1090_);
v___x_1095_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_nat_add(v_i_1072_, v_step_1074_);
lean_dec(v_i_1072_);
v___x_1097_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1068_, v___x_1069_, v_word_1062_, v_pattern_1063_, v_patternRoles_1064_, v_wordRoles_1065_, v___x_1066_, v___x_1067_, v_range_1070_, v___x_1095_, v___x_1096_);
return v___x_1097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* v_word_1102_, lean_object* v_pattern_1103_, lean_object* v_patternRoles_1104_, lean_object* v_wordRoles_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v_range_1110_, lean_object* v_b_1111_, lean_object* v_i_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1102_, v_pattern_1103_, v_patternRoles_1104_, v_wordRoles_1105_, v___x_1106_, v___x_1107_, v___x_1108_, v___x_1109_, v_range_1110_, v_b_1111_, v_i_1112_);
lean_dec_ref(v_range_1110_);
lean_dec(v___x_1109_);
lean_dec(v___x_1108_);
lean_dec(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_wordRoles_1105_);
lean_dec_ref(v_patternRoles_1104_);
lean_dec_ref(v_pattern_1103_);
lean_dec_ref(v_word_1102_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* v_wordRoles_1114_, lean_object* v_range_1115_, lean_object* v_b_1116_, lean_object* v_i_1117_){
_start:
{
lean_object* v_stop_1118_; lean_object* v_step_1119_; uint8_t v___x_1120_; 
v_stop_1118_ = lean_ctor_get(v_range_1115_, 1);
v_step_1119_ = lean_ctor_get(v_range_1115_, 2);
v___x_1120_ = lean_nat_dec_lt(v_i_1117_, v_stop_1118_);
if (v___x_1120_ == 0)
{
lean_dec(v_i_1117_);
return v_b_1116_;
}
else
{
lean_object* v_snd_1121_; lean_object* v_snd_1122_; lean_object* v_fst_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1179_; 
v_snd_1121_ = lean_ctor_get(v_b_1116_, 1);
lean_inc(v_snd_1121_);
v_snd_1122_ = lean_ctor_get(v_snd_1121_, 1);
lean_inc(v_snd_1122_);
v_fst_1123_ = lean_ctor_get(v_b_1116_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_b_1116_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v_b_1116_, 1);
lean_dec(v_unused_1180_);
v___x_1125_ = v_b_1116_;
v_isShared_1126_ = v_isSharedCheck_1179_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_fst_1123_);
lean_dec(v_b_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1179_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_fst_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1177_; 
v_fst_1127_ = lean_ctor_get(v_snd_1121_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_snd_1121_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v_snd_1121_, 1);
lean_dec(v_unused_1178_);
v___x_1129_ = v_snd_1121_;
v_isShared_1130_ = v_isSharedCheck_1177_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_fst_1127_);
lean_dec(v_snd_1121_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1177_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1176_; 
v_fst_1131_ = lean_ctor_get(v_snd_1122_, 0);
v_snd_1132_ = lean_ctor_get(v_snd_1122_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_snd_1122_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1134_ = v_snd_1122_;
v_isShared_1135_ = v_isSharedCheck_1176_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snd_1132_);
lean_inc(v_fst_1131_);
lean_dec(v_snd_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1176_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint8_t v___x_1136_; lean_object* v_lastSepIdx_1137_; lean_object* v_lastSepIdx_1139_; uint16_t v_penaltyNs_1140_; uint16_t v_penaltySkip_1141_; uint8_t v___x_1164_; 
v___x_1136_ = 0;
v_lastSepIdx_1137_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_nat_dec_eq(v_i_1117_, v_lastSepIdx_1137_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_box(v___x_1136_);
v___x_1166_ = lean_array_get(v___x_1165_, v_wordRoles_1114_, v_i_1117_);
lean_dec(v___x_1165_);
v___x_1167_ = lean_unbox(v___x_1166_);
lean_dec(v___x_1166_);
if (v___x_1167_ == 2)
{
uint16_t v_penaltyNs_1168_; uint16_t v___x_1169_; uint16_t v___x_1170_; uint16_t v___x_1171_; 
lean_dec(v_snd_1132_);
lean_dec(v_fst_1127_);
v_penaltyNs_1168_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1169_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1170_ = lean_unbox(v_fst_1131_);
lean_dec(v_fst_1131_);
v___x_1171_ = lean_int16_add(v___x_1170_, v___x_1169_);
lean_inc(v_i_1117_);
v_lastSepIdx_1139_ = v_i_1117_;
v_penaltyNs_1140_ = v___x_1171_;
v_penaltySkip_1141_ = v_penaltyNs_1168_;
goto v___jp_1138_;
}
else
{
uint16_t v___x_1172_; uint16_t v___x_1173_; 
v___x_1172_ = lean_unbox(v_fst_1131_);
lean_dec(v_fst_1131_);
v___x_1173_ = lean_unbox(v_snd_1132_);
lean_dec(v_snd_1132_);
v_lastSepIdx_1139_ = v_fst_1127_;
v_penaltyNs_1140_ = v___x_1172_;
v_penaltySkip_1141_ = v___x_1173_;
goto v___jp_1138_;
}
}
else
{
uint16_t v___x_1174_; uint16_t v___x_1175_; 
v___x_1174_ = lean_unbox(v_fst_1131_);
lean_dec(v_fst_1131_);
v___x_1175_ = lean_unbox(v_snd_1132_);
lean_dec(v_snd_1132_);
v_lastSepIdx_1139_ = v_fst_1127_;
v_penaltyNs_1140_ = v___x_1174_;
v_penaltySkip_1141_ = v___x_1175_;
goto v___jp_1138_;
}
v___jp_1138_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; uint8_t v___x_1145_; uint16_t v___x_1146_; uint16_t v___x_1147_; uint16_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1142_ = lean_box(v___x_1136_);
v___x_1143_ = lean_array_get(v___x_1142_, v_wordRoles_1114_, v_i_1117_);
lean_dec(v___x_1142_);
v___x_1144_ = lean_nat_dec_eq(v_i_1117_, v_lastSepIdx_1137_);
v___x_1145_ = lean_unbox(v___x_1143_);
lean_dec(v___x_1143_);
v___x_1146_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_1145_, v___x_1144_);
v___x_1147_ = lean_int16_add(v_penaltySkip_1141_, v___x_1146_);
v___x_1148_ = lean_int16_add(v___x_1147_, v_penaltyNs_1140_);
v___x_1149_ = lean_box(v___x_1148_);
v___x_1150_ = lean_array_set(v_fst_1123_, v_i_1117_, v___x_1149_);
v___x_1151_ = lean_box(v_penaltyNs_1140_);
v___x_1152_ = lean_box(v___x_1147_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1152_);
lean_ctor_set(v___x_1134_, 0, v___x_1151_);
v___x_1154_ = v___x_1134_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 1, v___x_1154_);
lean_ctor_set(v___x_1129_, 0, v_lastSepIdx_1139_);
v___x_1156_ = v___x_1129_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_lastSepIdx_1139_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1156_);
lean_ctor_set(v___x_1125_, 0, v___x_1150_);
v___x_1158_ = v___x_1125_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_nat_add(v_i_1117_, v_step_1119_);
lean_dec(v_i_1117_);
v_b_1116_ = v___x_1158_;
v_i_1117_ = v___x_1159_;
goto _start;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* v_wordRoles_1181_, lean_object* v_range_1182_, lean_object* v_b_1183_, lean_object* v_i_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1181_, v_range_1182_, v_b_1183_, v_i_1184_);
lean_dec_ref(v_range_1182_);
lean_dec_ref(v_wordRoles_1181_);
return v_res_1185_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0(void){
_start:
{
uint16_t v_penaltyNs_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_penaltyNs_1186_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1187_ = lean_box(v_penaltyNs_1186_);
v___x_1188_ = lean_box(v_penaltyNs_1186_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1(void){
_start:
{
lean_object* v___x_1190_; lean_object* v_lastSepIdx_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
v_lastSepIdx_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_lastSepIdx_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* v_pattern_1193_, lean_object* v_word_1194_, lean_object* v_patternRoles_1195_, lean_object* v_wordRoles_1196_){
_start:
{
uint16_t v___y_1198_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_lastSepIdx_1209_; uint16_t v_penaltyNs_1210_; lean_object* v___x_1211_; lean_object* v_runLengths_1212_; lean_object* v___x_1213_; lean_object* v_startPenalties_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_snd_1220_; lean_object* v_fst_1221_; lean_object* v_fst_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1252_; 
v___x_1204_ = lean_string_length(v_pattern_1193_);
v___x_1205_ = lean_string_length(v_word_1194_);
v___x_1206_ = lean_nat_mul(v___x_1204_, v___x_1205_);
v___x_1207_ = lean_unsigned_to_nat(2u);
v___x_1208_ = lean_nat_mul(v___x_1206_, v___x_1207_);
v_lastSepIdx_1209_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1210_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1211_ = lean_box(v_penaltyNs_1210_);
v_runLengths_1212_ = lean_mk_array(v___x_1206_, v___x_1211_);
v___x_1213_ = lean_box(v_penaltyNs_1210_);
v_startPenalties_1214_ = lean_mk_array(v___x_1205_, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1216_, 0, v_lastSepIdx_1209_);
lean_ctor_set(v___x_1216_, 1, v___x_1205_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
v___x_1217_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_startPenalties_1214_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1196_, v___x_1216_, v___x_1218_, v_lastSepIdx_1209_);
lean_dec_ref(v___x_1216_);
v_snd_1220_ = lean_ctor_get(v___x_1219_, 1);
lean_inc(v_snd_1220_);
v_fst_1221_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_fst_1221_);
lean_dec_ref(v___x_1219_);
v_fst_1222_ = lean_ctor_get(v_snd_1220_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_snd_1220_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_snd_1220_, 1);
lean_dec(v_unused_1253_);
v___x_1224_ = v_snd_1220_;
v_isShared_1225_ = v_isSharedCheck_1252_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_fst_1222_);
lean_dec(v_snd_1220_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1252_;
goto v_resetjp_1223_;
}
v___jp_1197_:
{
uint16_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1200_ = lean_int16_dec_le(v___y_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_int16_to_int(v___y_1198_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_box(0);
return v___x_1203_;
}
}
v_resetjp_1223_:
{
uint16_t v_matchScore_1226_; lean_object* v___x_1227_; lean_object* v_result_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_matchScore_1226_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1227_ = lean_box(v_matchScore_1226_);
v_result_1228_ = lean_mk_array(v___x_1208_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v_lastSepIdx_1209_);
lean_ctor_set(v___x_1229_, 1, v___x_1204_);
lean_ctor_set(v___x_1229_, 2, v___x_1215_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v_runLengths_1212_);
lean_ctor_set(v___x_1224_, 0, v_result_1228_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_result_1228_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_runLengths_1212_);
v___x_1231_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v_fst_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint16_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint16_t v___x_1246_; uint16_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1232_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1194_, v_pattern_1193_, v_patternRoles_1195_, v_wordRoles_1196_, v_fst_1221_, v_fst_1222_, v___x_1204_, v___x_1205_, v___x_1229_, v___x_1231_, v_lastSepIdx_1209_);
lean_dec_ref(v___x_1229_);
lean_dec(v_fst_1222_);
lean_dec(v_fst_1221_);
v_fst_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_fst_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = lean_nat_sub(v___x_1204_, v___x_1215_);
v___x_1235_ = lean_nat_sub(v___x_1205_, v___x_1215_);
v___x_1236_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1237_ = lean_nat_mul(v___x_1234_, v___x_1205_);
lean_dec(v___x_1234_);
v___x_1238_ = lean_nat_mul(v___x_1237_, v___x_1207_);
lean_dec(v___x_1237_);
v___x_1239_ = lean_nat_mul(v___x_1235_, v___x_1207_);
lean_dec(v___x_1235_);
v___x_1240_ = lean_nat_add(v___x_1238_, v___x_1239_);
lean_dec(v___x_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(v___x_1236_);
v___x_1242_ = lean_array_get(v___x_1241_, v_fst_1233_, v___x_1240_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_nat_add(v___x_1240_, v___x_1215_);
lean_dec(v___x_1240_);
v___x_1244_ = lean_box(v___x_1236_);
v___x_1245_ = lean_array_get(v___x_1244_, v_fst_1233_, v___x_1243_);
lean_dec(v___x_1243_);
lean_dec(v_fst_1233_);
lean_dec(v___x_1244_);
v___x_1246_ = lean_unbox(v___x_1242_);
v___x_1247_ = lean_unbox(v___x_1245_);
v___x_1248_ = lean_int16_dec_le(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
uint16_t v___x_1249_; 
lean_dec(v___x_1245_);
v___x_1249_ = lean_unbox(v___x_1242_);
lean_dec(v___x_1242_);
v___y_1198_ = v___x_1249_;
goto v___jp_1197_;
}
else
{
uint16_t v___x_1250_; 
lean_dec(v___x_1242_);
v___x_1250_ = lean_unbox(v___x_1245_);
lean_dec(v___x_1245_);
v___y_1198_ = v___x_1250_;
goto v___jp_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* v_pattern_1254_, lean_object* v_word_1255_, lean_object* v_patternRoles_1256_, lean_object* v_wordRoles_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1254_, v_word_1255_, v_patternRoles_1256_, v_wordRoles_1257_);
lean_dec_ref(v_wordRoles_1257_);
lean_dec_ref(v_patternRoles_1256_);
lean_dec_ref(v_word_1255_);
lean_dec_ref(v_pattern_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* v_wordRoles_1259_, lean_object* v_range_1260_, lean_object* v_b_1261_, lean_object* v_i_1262_, lean_object* v_hs_1263_, lean_object* v_hl_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1259_, v_range_1260_, v_b_1261_, v_i_1262_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* v_wordRoles_1266_, lean_object* v_range_1267_, lean_object* v_b_1268_, lean_object* v_i_1269_, lean_object* v_hs_1270_, lean_object* v_hl_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_1266_, v_range_1267_, v_b_1268_, v_i_1269_, v_hs_1270_, v_hl_1271_);
lean_dec_ref(v_range_1267_);
lean_dec_ref(v_wordRoles_1266_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* v_word_1273_, lean_object* v_a_1274_, lean_object* v_pattern_1275_, lean_object* v_patternRoles_1276_, lean_object* v_wordRoles_1277_, lean_object* v___x_1278_, lean_object* v___x_1279_, lean_object* v_range_1280_, lean_object* v_b_1281_, lean_object* v_i_1282_, lean_object* v_hs_1283_, lean_object* v_hl_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1273_, v_a_1274_, v_pattern_1275_, v_patternRoles_1276_, v_wordRoles_1277_, v___x_1278_, v___x_1279_, v_range_1280_, v_b_1281_, v_i_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* v_word_1286_, lean_object* v_a_1287_, lean_object* v_pattern_1288_, lean_object* v_patternRoles_1289_, lean_object* v_wordRoles_1290_, lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v_range_1293_, lean_object* v_b_1294_, lean_object* v_i_1295_, lean_object* v_hs_1296_, lean_object* v_hl_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v_word_1286_, v_a_1287_, v_pattern_1288_, v_patternRoles_1289_, v_wordRoles_1290_, v___x_1291_, v___x_1292_, v_range_1293_, v_b_1294_, v_i_1295_, v_hs_1296_, v_hl_1297_);
lean_dec_ref(v_range_1293_);
lean_dec(v___x_1292_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v_wordRoles_1290_);
lean_dec_ref(v_patternRoles_1289_);
lean_dec_ref(v_pattern_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_word_1286_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* v_word_1299_, lean_object* v_pattern_1300_, lean_object* v_patternRoles_1301_, lean_object* v_wordRoles_1302_, lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v_range_1307_, lean_object* v_b_1308_, lean_object* v_i_1309_, lean_object* v_hs_1310_, lean_object* v_hl_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1299_, v_pattern_1300_, v_patternRoles_1301_, v_wordRoles_1302_, v___x_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v_range_1307_, v_b_1308_, v_i_1309_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* v_word_1313_, lean_object* v_pattern_1314_, lean_object* v_patternRoles_1315_, lean_object* v_wordRoles_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v___x_1320_, lean_object* v_range_1321_, lean_object* v_b_1322_, lean_object* v_i_1323_, lean_object* v_hs_1324_, lean_object* v_hl_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v_word_1313_, v_pattern_1314_, v_patternRoles_1315_, v_wordRoles_1316_, v___x_1317_, v___x_1318_, v___x_1319_, v___x_1320_, v_range_1321_, v_b_1322_, v_i_1323_, v_hs_1324_, v_hl_1325_);
lean_dec_ref(v_range_1321_);
lean_dec(v___x_1320_);
lean_dec(v___x_1319_);
lean_dec(v___x_1318_);
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_wordRoles_1316_);
lean_dec_ref(v_patternRoles_1315_);
lean_dec_ref(v_pattern_1314_);
lean_dec_ref(v_word_1313_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_word_1329_, lean_object* v_pattern_1330_, lean_object* v_patternRoles_1331_, lean_object* v_wordRoles_1332_, lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v_range_1335_, lean_object* v_b_1336_, lean_object* v_i_1337_, lean_object* v_hs_1338_, lean_object* v_hl_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1327_, v___x_1328_, v_word_1329_, v_pattern_1330_, v_patternRoles_1331_, v_wordRoles_1332_, v___x_1333_, v___x_1334_, v_range_1335_, v_b_1336_, v_i_1337_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v_word_1343_, lean_object* v_pattern_1344_, lean_object* v_patternRoles_1345_, lean_object* v_wordRoles_1346_, lean_object* v___x_1347_, lean_object* v___x_1348_, lean_object* v_range_1349_, lean_object* v_b_1350_, lean_object* v_i_1351_, lean_object* v_hs_1352_, lean_object* v_hl_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(v___x_1341_, v___x_1342_, v_word_1343_, v_pattern_1344_, v_patternRoles_1345_, v_wordRoles_1346_, v___x_1347_, v___x_1348_, v_range_1349_, v_b_1350_, v_i_1351_, v_hs_1352_, v_hl_1353_);
lean_dec_ref(v_range_1349_);
lean_dec(v___x_1348_);
lean_dec_ref(v___x_1347_);
lean_dec_ref(v_wordRoles_1346_);
lean_dec_ref(v_patternRoles_1345_);
lean_dec_ref(v_pattern_1344_);
lean_dec_ref(v_word_1343_);
lean_dec(v___x_1342_);
lean_dec(v___x_1341_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_nat_to_int(v_a_1355_);
return v___x_1356_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1357_; double v___x_1358_; 
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_float_of_nat(v___x_1357_);
return v___x_1358_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1(void){
_start:
{
lean_object* v___x_1359_; double v___x_1360_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_float_of_nat(v___x_1359_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_unsigned_to_nat(2u);
v___x_1362_ = lean_nat_to_int(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1(void){
_start:
{
double v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1364_ = lean_box_float(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* v_pattern_1367_, lean_object* v_word_1368_){
_start:
{
double v___y_1370_; double v___y_1371_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = lean_string_utf8_byte_size(v_pattern_1367_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_nat_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_score_1383_; uint8_t v___x_1399_; 
v___x_1380_ = lean_string_length(v_word_1368_);
v___x_1381_ = lean_string_length(v_pattern_1367_);
v___x_1399_ = lean_nat_dec_lt(v___x_1380_, v___x_1381_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
v___x_1400_ = l_String_charactersIn(v_pattern_1367_, v_word_1368_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_box(0);
return v___x_1401_;
}
else
{
if (v___x_1379_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_1367_);
v___x_1403_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_1368_);
v___x_1404_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1367_, v_word_1368_, v___x_1402_, v___x_1403_);
lean_dec_ref(v___x_1403_);
lean_dec_ref(v___x_1402_);
if (lean_obj_tag(v___x_1404_) == 1)
{
lean_object* v_val_1405_; uint8_t v___x_1406_; 
v_val_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = lean_nat_dec_eq(v___x_1381_, v___x_1380_);
if (v___x_1406_ == 0)
{
v_score_1383_ = v_val_1405_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1407_; lean_object* v_score_1408_; 
v___x_1407_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
v_score_1408_ = lean_int_mul(v_val_1405_, v___x_1407_);
lean_dec(v_val_1405_);
v_score_1383_ = v_score_1408_;
goto v___jp_1382_;
}
}
else
{
lean_object* v___x_1409_; 
lean_dec(v___x_1404_);
v___x_1409_ = lean_box(0);
return v___x_1409_;
}
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
}
}
else
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_box(0);
return v___x_1411_;
}
v___jp_1382_:
{
lean_object* v_perfect_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_perfectMatch_1391_; double v___x_1392_; lean_object* v___x_1393_; double v___x_1394_; double v_normScore_1395_; double v___x_1396_; double v___x_1397_; uint8_t v___x_1398_; 
v_perfect_1384_ = lean_unsigned_to_nat(4u);
v___x_1385_ = lean_nat_mul(v_perfect_1384_, v___x_1381_);
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v___x_1381_, v___x_1386_);
v___x_1388_ = lean_nat_mul(v___x_1381_, v___x_1387_);
lean_dec(v___x_1387_);
v___x_1389_ = lean_nat_shiftr(v___x_1388_, v___x_1386_);
lean_dec(v___x_1388_);
v___x_1390_ = lean_nat_sub(v___x_1389_, v___x_1386_);
lean_dec(v___x_1389_);
v_perfectMatch_1391_ = lean_nat_add(v___x_1385_, v___x_1390_);
lean_dec(v___x_1390_);
lean_dec(v___x_1385_);
v___x_1392_ = l_Float_ofInt(v_score_1383_);
lean_dec(v_score_1383_);
v___x_1393_ = lean_nat_to_int(v_perfectMatch_1391_);
v___x_1394_ = l_Float_ofInt(v___x_1393_);
lean_dec(v___x_1393_);
v_normScore_1395_ = lean_float_div(v___x_1392_, v___x_1394_);
v___x_1396_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1397_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1);
v___x_1398_ = lean_float_decLe(v___x_1397_, v_normScore_1395_);
if (v___x_1398_ == 0)
{
v___y_1370_ = v___x_1396_;
v___y_1371_ = v___x_1397_;
goto v___jp_1369_;
}
else
{
v___y_1370_ = v___x_1396_;
v___y_1371_ = v_normScore_1395_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return v___x_1412_;
}
v___jp_1369_:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_float_decLe(v___y_1370_, v___y_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box_float(v___y_1371_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_box_float(v___y_1370_);
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* v_pattern_1413_, lean_object* v_word_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1413_, v_word_1414_);
lean_dec_ref(v_word_1414_);
lean_dec_ref(v_pattern_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* v_pattern_1416_, lean_object* v_word_1417_, double v_threshold_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1416_, v_word_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; double v___x_1421_; uint8_t v___x_1422_; 
v_val_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1420_);
v___x_1421_ = lean_unbox_float(v_val_1420_);
lean_dec(v_val_1420_);
v___x_1422_ = lean_float_decLt(v_threshold_1418_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v___x_1419_);
v___x_1423_ = lean_box(0);
return v___x_1423_;
}
else
{
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* v_pattern_1424_, lean_object* v_word_1425_, lean_object* v_threshold_1426_){
_start:
{
double v_threshold_boxed_1427_; lean_object* v_res_1428_; 
v_threshold_boxed_1427_ = lean_unbox_float(v_threshold_1426_);
lean_dec_ref(v_threshold_1426_);
v_res_1428_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1424_, v_word_1425_, v_threshold_boxed_1427_);
lean_dec_ref(v_word_1425_);
lean_dec_ref(v_pattern_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* v_pattern_1429_, lean_object* v_word_1430_, double v_threshold_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1429_, v_word_1430_, v_threshold_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = 0;
return v___x_1433_;
}
else
{
uint8_t v___x_1434_; 
lean_dec_ref(v___x_1432_);
v___x_1434_ = 1;
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* v_pattern_1435_, lean_object* v_word_1436_, lean_object* v_threshold_1437_){
_start:
{
double v_threshold_boxed_1438_; uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_threshold_boxed_1438_ = lean_unbox_float(v_threshold_1437_);
lean_dec_ref(v_threshold_1437_);
v_res_1439_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1435_, v_word_1436_, v_threshold_boxed_1438_);
lean_dec_ref(v_word_1436_);
lean_dec_ref(v_pattern_1435_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_FuzzyMatching(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_FuzzyMatching_instInhabitedCharRole_default = _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default();
l_Lean_FuzzyMatching_instInhabitedCharRole = _init_l_Lean_FuzzyMatching_instInhabitedCharRole();
l_Lean_FuzzyMatching_instInhabitedScore_default = _init_l_Lean_FuzzyMatching_instInhabitedScore_default();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore();
l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful = _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful();
l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1 = _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_FuzzyMatching(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
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
res = initialize_Lean_Server_Completion_CompletionUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_FuzzyMatching(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_FuzzyMatching(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_FuzzyMatching(builtin);
}
#ifdef __cplusplus
}
#endif
