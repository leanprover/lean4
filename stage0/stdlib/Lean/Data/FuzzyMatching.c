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
uint8_t l_Lean_String_charactersIn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg(lean_object* v_k_143_){
_start:
{
lean_inc(v_k_143_);
return v_k_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(lean_object* v_k_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_FuzzyMatching_CharType_ctorElim___redArg(v_k_144_);
lean_dec(v_k_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim(lean_object* v_motive_146_, lean_object* v_ctorIdx_147_, uint8_t v_t_148_, lean_object* v_h_149_, lean_object* v_k_150_){
_start:
{
lean_inc(v_k_150_);
return v_k_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___boxed(lean_object* v_motive_151_, lean_object* v_ctorIdx_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_k_155_){
_start:
{
uint8_t v_t_boxed_156_; lean_object* v_res_157_; 
v_t_boxed_156_ = lean_unbox(v_t_153_);
v_res_157_ = l_Lean_FuzzyMatching_CharType_ctorElim(v_motive_151_, v_ctorIdx_152_, v_t_boxed_156_, v_h_154_, v_k_155_);
lean_dec(v_k_155_);
lean_dec(v_ctorIdx_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg(lean_object* v_lower_158_){
_start:
{
lean_inc(v_lower_158_);
return v_lower_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(lean_object* v_lower_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_FuzzyMatching_CharType_lower_elim___redArg(v_lower_159_);
lean_dec(v_lower_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim(lean_object* v_motive_161_, uint8_t v_t_162_, lean_object* v_h_163_, lean_object* v_lower_164_){
_start:
{
lean_inc(v_lower_164_);
return v_lower_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___boxed(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_lower_168_){
_start:
{
uint8_t v_t_boxed_169_; lean_object* v_res_170_; 
v_t_boxed_169_ = lean_unbox(v_t_166_);
v_res_170_ = l_Lean_FuzzyMatching_CharType_lower_elim(v_motive_165_, v_t_boxed_169_, v_h_167_, v_lower_168_);
lean_dec(v_lower_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg(lean_object* v_upper_171_){
_start:
{
lean_inc(v_upper_171_);
return v_upper_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(lean_object* v_upper_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_FuzzyMatching_CharType_upper_elim___redArg(v_upper_172_);
lean_dec(v_upper_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim(lean_object* v_motive_174_, uint8_t v_t_175_, lean_object* v_h_176_, lean_object* v_upper_177_){
_start:
{
lean_inc(v_upper_177_);
return v_upper_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___boxed(lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_upper_181_){
_start:
{
uint8_t v_t_boxed_182_; lean_object* v_res_183_; 
v_t_boxed_182_ = lean_unbox(v_t_179_);
v_res_183_ = l_Lean_FuzzyMatching_CharType_upper_elim(v_motive_178_, v_t_boxed_182_, v_h_180_, v_upper_181_);
lean_dec(v_upper_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg(lean_object* v_separator_184_){
_start:
{
lean_inc(v_separator_184_);
return v_separator_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg___boxed(lean_object* v_separator_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_FuzzyMatching_CharType_separator_elim___redArg(v_separator_185_);
lean_dec(v_separator_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim(lean_object* v_motive_187_, uint8_t v_t_188_, lean_object* v_h_189_, lean_object* v_separator_190_){
_start:
{
lean_inc(v_separator_190_);
return v_separator_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___boxed(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_separator_194_){
_start:
{
uint8_t v_t_boxed_195_; lean_object* v_res_196_; 
v_t_boxed_195_ = lean_unbox(v_t_192_);
v_res_196_ = l_Lean_FuzzyMatching_CharType_separator_elim(v_motive_191_, v_t_boxed_195_, v_h_193_, v_separator_194_);
lean_dec(v_separator_194_);
return v_res_196_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charType(uint32_t v_c_197_){
_start:
{
uint8_t v___y_207_; uint8_t v___y_210_; uint32_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = 65;
v___x_221_ = lean_uint32_dec_le(v___x_220_, v_c_197_);
if (v___x_221_ == 0)
{
goto v___jp_215_;
}
else
{
uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 90;
v___x_223_ = lean_uint32_dec_le(v_c_197_, v___x_222_);
if (v___x_223_ == 0)
{
goto v___jp_215_;
}
else
{
goto v___jp_198_;
}
}
v___jp_198_:
{
uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 65;
v___x_200_ = lean_uint32_dec_le(v___x_199_, v_c_197_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
else
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 90;
v___x_203_ = lean_uint32_dec_le(v_c_197_, v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
else
{
uint8_t v___x_205_; 
v___x_205_ = 1;
return v___x_205_;
}
}
}
v___jp_206_:
{
if (v___y_207_ == 0)
{
uint8_t v___x_208_; 
v___x_208_ = 2;
return v___x_208_;
}
else
{
goto v___jp_198_;
}
}
v___jp_209_:
{
if (v___y_210_ == 0)
{
uint32_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 48;
v___x_212_ = lean_uint32_dec_le(v___x_211_, v_c_197_);
if (v___x_212_ == 0)
{
v___y_207_ = v___x_212_;
goto v___jp_206_;
}
else
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 57;
v___x_214_ = lean_uint32_dec_le(v_c_197_, v___x_213_);
v___y_207_ = v___x_214_;
goto v___jp_206_;
}
}
else
{
goto v___jp_198_;
}
}
v___jp_215_:
{
uint32_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = 97;
v___x_217_ = lean_uint32_dec_le(v___x_216_, v_c_197_);
if (v___x_217_ == 0)
{
v___y_210_ = v___x_217_;
goto v___jp_209_;
}
else
{
uint32_t v___x_218_; uint8_t v___x_219_; 
v___x_218_ = 122;
v___x_219_ = lean_uint32_dec_le(v_c_197_, v___x_218_);
v___y_210_ = v___x_219_;
goto v___jp_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charType___boxed(lean_object* v_c_224_){
_start:
{
uint32_t v_c_boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v_c_boxed_225_ = lean_unbox_uint32(v_c_224_);
lean_dec(v_c_224_);
v_res_226_ = l_Lean_FuzzyMatching_charType(v_c_boxed_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx(uint8_t v_x_228_){
_start:
{
switch(v_x_228_)
{
case 0:
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
return v___x_229_;
}
case 1:
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(1u);
return v___x_230_;
}
default: 
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(2u);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___boxed(lean_object* v_x_232_){
_start:
{
uint8_t v_x_boxed_233_; lean_object* v_res_234_; 
v_x_boxed_233_ = lean_unbox(v_x_232_);
v_res_234_ = l_Lean_FuzzyMatching_CharRole_ctorIdx(v_x_boxed_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(lean_object* v_k_235_){
_start:
{
lean_inc(v_k_235_);
return v_k_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(lean_object* v_k_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(v_k_236_);
lean_dec(v_k_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object* v_motive_238_, lean_object* v_ctorIdx_239_, uint8_t v_t_240_, lean_object* v_h_241_, lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
uint8_t v_t_boxed_248_; lean_object* v_res_249_; 
v_t_boxed_248_ = lean_unbox(v_t_245_);
v_res_249_ = l_Lean_FuzzyMatching_CharRole_ctorElim(v_motive_243_, v_ctorIdx_244_, v_t_boxed_248_, v_h_246_, v_k_247_);
lean_dec(v_k_247_);
lean_dec(v_ctorIdx_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object* v_head_250_){
_start:
{
lean_inc(v_head_250_);
return v_head_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object* v_head_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(v_head_251_);
lean_dec(v_head_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object* v_motive_253_, uint8_t v_t_254_, lean_object* v_h_255_, lean_object* v_head_256_){
_start:
{
lean_inc(v_head_256_);
return v_head_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object* v_motive_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_head_260_){
_start:
{
uint8_t v_t_boxed_261_; lean_object* v_res_262_; 
v_t_boxed_261_ = lean_unbox(v_t_258_);
v_res_262_ = l_Lean_FuzzyMatching_CharRole_head_elim(v_motive_257_, v_t_boxed_261_, v_h_259_, v_head_260_);
lean_dec(v_head_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object* v_tail_263_){
_start:
{
lean_inc(v_tail_263_);
return v_tail_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object* v_tail_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(v_tail_264_);
lean_dec(v_tail_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object* v_motive_266_, uint8_t v_t_267_, lean_object* v_h_268_, lean_object* v_tail_269_){
_start:
{
lean_inc(v_tail_269_);
return v_tail_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_tail_273_){
_start:
{
uint8_t v_t_boxed_274_; lean_object* v_res_275_; 
v_t_boxed_274_ = lean_unbox(v_t_271_);
v_res_275_ = l_Lean_FuzzyMatching_CharRole_tail_elim(v_motive_270_, v_t_boxed_274_, v_h_272_, v_tail_273_);
lean_dec(v_tail_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object* v_separator_276_){
_start:
{
lean_inc(v_separator_276_);
return v_separator_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object* v_separator_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(v_separator_277_);
lean_dec(v_separator_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object* v_motive_279_, uint8_t v_t_280_, lean_object* v_h_281_, lean_object* v_separator_282_){
_start:
{
lean_inc(v_separator_282_);
return v_separator_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object* v_motive_283_, lean_object* v_t_284_, lean_object* v_h_285_, lean_object* v_separator_286_){
_start:
{
uint8_t v_t_boxed_287_; lean_object* v_res_288_; 
v_t_boxed_287_ = lean_unbox(v_t_284_);
v_res_288_ = l_Lean_FuzzyMatching_CharRole_separator_elim(v_motive_283_, v_t_boxed_287_, v_h_285_, v_separator_286_);
lean_dec(v_separator_286_);
return v_res_288_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default(void){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole(void){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = 0;
return v___x_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object* v_prev_x3f_291_, uint8_t v_curr_292_, lean_object* v_next_x3f_293_){
_start:
{
if (v_curr_292_ == 2)
{
uint8_t v___x_294_; 
v___x_294_ = 2;
return v___x_294_;
}
else
{
if (lean_obj_tag(v_prev_x3f_291_) == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
else
{
lean_object* v_val_296_; uint8_t v___x_297_; 
v_val_296_ = lean_ctor_get(v_prev_x3f_291_, 0);
v___x_297_ = lean_unbox(v_val_296_);
if (v___x_297_ == 2)
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
else
{
if (v_curr_292_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 1;
return v___x_299_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = lean_unbox(v_val_296_);
if (v___x_300_ == 1)
{
if (lean_obj_tag(v_next_x3f_293_) == 1)
{
lean_object* v_val_301_; uint8_t v___x_302_; 
v_val_301_ = lean_ctor_get(v_next_x3f_293_, 0);
v___x_302_ = lean_unbox(v_val_301_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 0;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 1;
return v___x_305_;
}
}
else
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object* v_prev_x3f_307_, lean_object* v_curr_308_, lean_object* v_next_x3f_309_){
_start:
{
uint8_t v_curr_boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_curr_boxed_310_ = lean_unbox(v_curr_308_);
v_res_311_ = l_Lean_FuzzyMatching_charRole(v_prev_x3f_307_, v_curr_boxed_310_, v_next_x3f_309_);
lean_dec(v_next_x3f_309_);
lean_dec(v_prev_x3f_307_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_string_313_, lean_object* v_range_314_, lean_object* v_b_315_, lean_object* v_i_316_){
_start:
{
lean_object* v_stop_317_; lean_object* v_step_318_; uint8_t v___y_320_; uint8_t v___x_325_; 
v_stop_317_ = lean_ctor_get(v_range_314_, 1);
v_step_318_ = lean_ctor_get(v_range_314_, 2);
v___x_325_ = lean_nat_dec_lt(v_i_316_, v_stop_317_);
if (v___x_325_ == 0)
{
lean_dec(v_i_316_);
return v_b_315_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; uint32_t v___x_328_; uint8_t v___x_329_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_sub(v_i_316_, v___x_326_);
v___x_328_ = lean_string_utf8_get(v_string_313_, v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = l_Lean_FuzzyMatching_charType(v___x_328_);
if (v___x_329_ == 2)
{
uint8_t v___x_330_; 
v___x_330_ = 2;
v___y_320_ = v___x_330_;
goto v___jp_319_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_331_ = lean_unsigned_to_nat(2u);
v___x_332_ = lean_nat_sub(v_i_316_, v___x_331_);
v___x_333_ = lean_string_utf8_get(v_string_313_, v___x_332_);
lean_dec(v___x_332_);
v___x_334_ = l_Lean_FuzzyMatching_charType(v___x_333_);
if (v___x_334_ == 2)
{
uint8_t v___x_335_; 
v___x_335_ = 0;
v___y_320_ = v___x_335_;
goto v___jp_319_;
}
else
{
if (v___x_329_ == 0)
{
uint8_t v___x_336_; 
v___x_336_ = 1;
v___y_320_ = v___x_336_;
goto v___jp_319_;
}
else
{
if (v___x_334_ == 1)
{
uint32_t v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_string_utf8_get(v_string_313_, v_i_316_);
v___x_338_ = l_Lean_FuzzyMatching_charType(v___x_337_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; 
v___x_339_ = 0;
v___y_320_ = v___x_339_;
goto v___jp_319_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 1;
v___y_320_ = v___x_340_;
goto v___jp_319_;
}
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
v___y_320_ = v___x_341_;
goto v___jp_319_;
}
}
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_box(v___y_320_);
v___x_322_ = lean_array_push(v_b_315_, v___x_321_);
v___x_323_ = lean_nat_add(v_i_316_, v_step_318_);
lean_dec(v_i_316_);
v_b_315_ = v___x_322_;
v_i_316_ = v___x_323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_string_342_, lean_object* v_range_343_, lean_object* v_b_344_, lean_object* v_i_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_342_, v_range_343_, v_b_344_, v_i_345_);
lean_dec_ref(v_range_343_);
lean_dec_ref(v_string_342_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object* v_string_347_, lean_object* v_range_348_, lean_object* v_b_349_, lean_object* v_i_350_){
_start:
{
lean_object* v_stop_351_; lean_object* v_step_352_; uint8_t v___y_354_; uint8_t v___x_359_; 
v_stop_351_ = lean_ctor_get(v_range_348_, 1);
v_step_352_ = lean_ctor_get(v_range_348_, 2);
v___x_359_ = lean_nat_dec_lt(v_i_350_, v_stop_351_);
if (v___x_359_ == 0)
{
return v_b_349_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_sub(v_i_350_, v___x_360_);
v___x_362_ = lean_string_utf8_get(v_string_347_, v___x_361_);
lean_dec(v___x_361_);
v___x_363_ = l_Lean_FuzzyMatching_charType(v___x_362_);
if (v___x_363_ == 2)
{
uint8_t v___x_364_; 
v___x_364_ = 2;
v___y_354_ = v___x_364_;
goto v___jp_353_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_365_ = lean_unsigned_to_nat(2u);
v___x_366_ = lean_nat_sub(v_i_350_, v___x_365_);
v___x_367_ = lean_string_utf8_get(v_string_347_, v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = l_Lean_FuzzyMatching_charType(v___x_367_);
if (v___x_368_ == 2)
{
uint8_t v___x_369_; 
v___x_369_ = 0;
v___y_354_ = v___x_369_;
goto v___jp_353_;
}
else
{
if (v___x_363_ == 0)
{
uint8_t v___x_370_; 
v___x_370_ = 1;
v___y_354_ = v___x_370_;
goto v___jp_353_;
}
else
{
if (v___x_368_ == 1)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_string_utf8_get(v_string_347_, v_i_350_);
v___x_372_ = l_Lean_FuzzyMatching_charType(v___x_371_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; 
v___x_373_ = 0;
v___y_354_ = v___x_373_;
goto v___jp_353_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = 1;
v___y_354_ = v___x_374_;
goto v___jp_353_;
}
}
else
{
uint8_t v___x_375_; 
v___x_375_ = 0;
v___y_354_ = v___x_375_;
goto v___jp_353_;
}
}
}
}
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_box(v___y_354_);
v___x_356_ = lean_array_push(v_b_349_, v___x_355_);
v___x_357_ = lean_nat_add(v_i_350_, v_step_352_);
v___x_358_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_347_, v_range_348_, v___x_356_, v___x_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object* v_string_376_, lean_object* v_range_377_, lean_object* v_b_378_, lean_object* v_i_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_376_, v_range_377_, v_b_378_, v_i_379_);
lean_dec(v_i_379_);
lean_dec_ref(v_range_377_);
lean_dec_ref(v_string_376_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object* v_prev_x3f_381_, uint32_t v_curr_382_, lean_object* v_next_x3f_383_){
_start:
{
lean_object* v___y_385_; uint8_t v___y_386_; lean_object* v___y_387_; lean_object* v___y_402_; 
if (lean_obj_tag(v_prev_x3f_381_) == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
v___y_402_ = v___x_416_;
goto v___jp_401_;
}
else
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_427_; 
v_val_417_ = lean_ctor_get(v_prev_x3f_381_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_prev_x3f_381_);
if (v_isSharedCheck_427_ == 0)
{
v___x_419_ = v_prev_x3f_381_;
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v_prev_x3f_381_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint32_t v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_421_ = lean_unbox_uint32(v_val_417_);
lean_dec(v_val_417_);
v___x_422_ = l_Lean_FuzzyMatching_charType(v___x_421_);
v___x_423_ = lean_box(v___x_422_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_423_);
v___x_425_ = v___x_419_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
v___y_402_ = v___x_425_;
goto v___jp_401_;
}
}
}
v___jp_384_:
{
if (v___y_386_ == 2)
{
uint8_t v___x_388_; 
lean_dec(v___y_387_);
lean_dec(v___y_385_);
v___x_388_ = 2;
return v___x_388_;
}
else
{
if (lean_obj_tag(v___y_385_) == 0)
{
uint8_t v___x_389_; 
lean_dec(v___y_387_);
v___x_389_ = 0;
return v___x_389_;
}
else
{
lean_object* v_val_390_; uint8_t v___x_391_; 
v_val_390_ = lean_ctor_get(v___y_385_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___y_385_, 1);
v___x_391_ = lean_unbox(v_val_390_);
if (v___x_391_ == 2)
{
uint8_t v___x_392_; 
lean_dec(v_val_390_);
lean_dec(v___y_387_);
v___x_392_ = 0;
return v___x_392_;
}
else
{
if (v___y_386_ == 0)
{
uint8_t v___x_393_; 
lean_dec(v_val_390_);
lean_dec(v___y_387_);
v___x_393_ = 1;
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = lean_unbox(v_val_390_);
lean_dec(v_val_390_);
if (v___x_394_ == 1)
{
if (lean_obj_tag(v___y_387_) == 1)
{
lean_object* v_val_395_; uint8_t v___x_396_; 
v_val_395_ = lean_ctor_get(v___y_387_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___y_387_, 1);
v___x_396_ = lean_unbox(v_val_395_);
lean_dec(v_val_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 1;
return v___x_398_;
}
}
else
{
uint8_t v___x_399_; 
lean_dec(v___y_387_);
v___x_399_ = 1;
return v___x_399_;
}
}
else
{
uint8_t v___x_400_; 
lean_dec(v___y_387_);
v___x_400_ = 0;
return v___x_400_;
}
}
}
}
}
}
v___jp_401_:
{
uint8_t v___x_403_; 
v___x_403_ = l_Lean_FuzzyMatching_charType(v_curr_382_);
if (lean_obj_tag(v_next_x3f_383_) == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_box(0);
v___y_385_ = v___y_402_;
v___y_386_ = v___x_403_;
v___y_387_ = v___x_404_;
goto v___jp_384_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_415_; 
v_val_405_ = lean_ctor_get(v_next_x3f_383_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_next_x3f_383_);
if (v_isSharedCheck_415_ == 0)
{
v___x_407_ = v_next_x3f_383_;
v_isShared_408_ = v_isSharedCheck_415_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v_next_x3f_383_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_415_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint32_t v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_409_ = lean_unbox_uint32(v_val_405_);
lean_dec(v_val_405_);
v___x_410_ = l_Lean_FuzzyMatching_charType(v___x_409_);
v___x_411_ = lean_box(v___x_410_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_411_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
v___y_385_ = v___y_402_;
v___y_386_ = v___x_403_;
v___y_387_ = v___x_413_;
goto v___jp_384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* v_prev_x3f_428_, lean_object* v_curr_429_, lean_object* v_next_x3f_430_){
_start:
{
uint32_t v_curr_boxed_431_; uint8_t v_res_432_; lean_object* v_r_433_; 
v_curr_boxed_431_ = lean_unbox_uint32(v_curr_429_);
lean_dec(v_curr_429_);
v_res_432_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_428_, v_curr_boxed_431_, v_next_x3f_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* v_string_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_string_utf8_byte_size(v_string_436_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_string_length(v_string_436_);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v_result_443_; lean_object* v___x_444_; uint32_t v___x_445_; uint32_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v_result_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint32_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint32_t v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_result_443_ = lean_mk_empty_array_with_capacity(v___x_440_);
v___x_444_ = lean_box(0);
v___x_445_ = lean_string_utf8_get(v_string_436_, v___x_438_);
v___x_446_ = lean_string_utf8_get(v_string_436_, v___x_441_);
v___x_447_ = lean_box_uint32(v___x_446_);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
v___x_449_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_444_, v___x_445_, v___x_448_);
v___x_450_ = lean_box(v___x_449_);
v_result_451_ = lean_array_push(v_result_443_, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_440_);
lean_ctor_set(v___x_453_, 2, v___x_441_);
v___x_454_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_436_, v___x_453_, v_result_451_, v___x_452_);
lean_dec_ref_known(v___x_453_, 3);
v___x_455_ = lean_nat_sub(v___x_440_, v___x_452_);
v___x_456_ = lean_string_utf8_get(v_string_436_, v___x_455_);
lean_dec(v___x_455_);
v___x_457_ = lean_box_uint32(v___x_456_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___x_459_ = lean_nat_sub(v___x_440_, v___x_441_);
v___x_460_ = lean_string_utf8_get(v_string_436_, v___x_459_);
lean_dec(v___x_459_);
v___x_461_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_458_, v___x_460_, v___x_444_);
v___x_462_ = lean_box(v___x_461_);
v___x_463_ = lean_array_push(v___x_454_, v___x_462_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; uint32_t v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_string_utf8_get(v_string_436_, v___x_438_);
v___x_466_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_464_, v___x_465_, v___x_464_);
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_468_ = lean_box(v___x_466_);
v___x_469_ = lean_array_push(v___x_467_, v___x_468_);
return v___x_469_;
}
}
else
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0));
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* v_string_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_471_);
lean_dec_ref(v_string_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* v_s_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* v_s_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_475_);
lean_dec_ref(v_s_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* v_string_477_, lean_object* v_range_478_, lean_object* v_b_479_, lean_object* v_i_480_, lean_object* v_hs_481_, lean_object* v_hl_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_477_, v_range_478_, v_b_479_, v_i_480_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* v_string_484_, lean_object* v_range_485_, lean_object* v_b_486_, lean_object* v_i_487_, lean_object* v_hs_488_, lean_object* v_hl_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_484_, v_range_485_, v_b_486_, v_i_487_, v_hs_488_, v_hl_489_);
lean_dec(v_i_487_);
lean_dec_ref(v_range_485_);
lean_dec_ref(v_string_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* v_string_491_, lean_object* v_range_492_, lean_object* v_b_493_, lean_object* v_i_494_, lean_object* v_hs_495_, lean_object* v_hl_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_491_, v_range_492_, v_b_493_, v_i_494_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_string_498_, lean_object* v_range_499_, lean_object* v_b_500_, lean_object* v_i_501_, lean_object* v_hs_502_, lean_object* v_hl_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_498_, v_range_499_, v_b_500_, v_i_501_, v_hs_502_, v_hl_503_);
lean_dec_ref(v_range_499_);
lean_dec_ref(v_string_498_);
return v_res_504_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0(void){
_start:
{
lean_object* v___x_505_; uint16_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_int16_of_nat(v___x_505_);
return v___x_506_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default(void){
_start:
{
uint16_t v___x_507_; 
v___x_507_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_507_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore(void){
_start:
{
uint16_t v___x_508_; 
v___x_508_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
return v___x_508_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0(void){
_start:
{
lean_object* v___x_509_; uint16_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(32768u);
v___x_510_ = lean_int16_of_nat(v___x_509_);
return v___x_510_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1(void){
_start:
{
uint16_t v___x_511_; uint16_t v___x_512_; 
v___x_511_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0);
v___x_512_ = lean_int16_neg(v___x_511_);
return v___x_512_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful(void){
_start:
{
uint16_t v___x_513_; 
v___x_513_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
return v___x_513_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t v_x_514_){
_start:
{
uint16_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_516_ = lean_int16_dec_le(v_x_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* v_x_517_){
_start:
{
uint16_t v_x_boxed_518_; uint8_t v_res_519_; lean_object* v_r_520_; 
v_x_boxed_518_ = lean_unbox(v_x_517_);
v_res_519_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t v_x_521_, lean_object* v_f_522_){
_start:
{
uint16_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_524_ = lean_int16_dec_le(v_x_521_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; uint16_t v___x_527_; 
v___x_525_ = lean_box(v_x_521_);
v___x_526_ = lean_apply_1(v_f_522_, v___x_525_);
v___x_527_ = lean_unbox(v___x_526_);
return v___x_527_;
}
else
{
lean_dec_ref(v_f_522_);
return v_x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* v_x_528_, lean_object* v_f_529_){
_start:
{
uint16_t v_x_boxed_530_; uint16_t v_res_531_; lean_object* v_r_532_; 
v_x_boxed_530_ = lean_unbox(v_x_528_);
v_res_531_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_boxed_530_, v_f_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t v_x_533_){
_start:
{
uint16_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_535_ = lean_int16_dec_le(v_x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_box(v_x_533_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* v_x_539_){
_start:
{
uint16_t v_x_boxed_540_; lean_object* v_res_541_; 
v_x_boxed_540_ = lean_unbox(v_x_539_);
v_res_541_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_boxed_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t v_x_542_){
_start:
{
uint16_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_544_ = lean_int16_dec_le(v_x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_int16_to_int(v_x_542_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* v_x_548_){
_start:
{
uint16_t v_x_boxed_549_; lean_object* v_res_550_; 
v_x_boxed_549_ = lean_unbox(v_x_548_);
v_res_550_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_549_);
return v_res_550_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
v___x_555_ = lean_unsigned_to_nat(2u);
v___x_556_ = lean_unsigned_to_nat(127u);
v___x_557_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
v___x_558_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
v___x_559_ = l_mkPanicMessageWithDecl(v___x_558_, v___x_557_, v___x_556_, v___x_555_, v___x_554_);
return v___x_559_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t v_x_560_){
_start:
{
uint16_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_562_ = lean_int16_dec_eq(v_x_560_, v___x_561_);
if (v___x_562_ == 0)
{
return v_x_560_;
}
else
{
uint16_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint16_t v___x_567_; 
v___x_563_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_564_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_565_ = lean_box(v___x_563_);
v___x_566_ = l_panic___redArg(v___x_565_, v___x_564_);
lean_dec(v___x_565_);
v___x_567_ = lean_unbox(v___x_566_);
lean_dec(v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* v_x_568_){
_start:
{
uint16_t v_x_boxed_569_; uint16_t v_res_570_; lean_object* v_r_571_; 
v_x_boxed_569_ = lean_unbox(v_x_568_);
v_res_570_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_boxed_569_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t v_missScore_572_, uint16_t v_matchScore_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_int16_dec_le(v_missScore_572_, v_matchScore_573_);
if (v___x_574_ == 0)
{
return v_missScore_572_;
}
else
{
return v_matchScore_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* v_missScore_575_, lean_object* v_matchScore_576_){
_start:
{
uint16_t v_missScore_boxed_577_; uint16_t v_matchScore_boxed_578_; uint16_t v_res_579_; lean_object* v_r_580_; 
v_missScore_boxed_577_ = lean_unbox(v_missScore_575_);
v_matchScore_boxed_578_ = lean_unbox(v_matchScore_576_);
v_res_579_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_boxed_577_, v_matchScore_boxed_578_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* v_word_581_, lean_object* v_patternIdx_582_, lean_object* v_wordIdx_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_584_ = lean_string_length(v_word_581_);
v___x_585_ = lean_nat_mul(v_patternIdx_582_, v___x_584_);
v___x_586_ = lean_unsigned_to_nat(2u);
v___x_587_ = lean_nat_mul(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_nat_mul(v_wordIdx_583_, v___x_586_);
v___x_589_ = lean_nat_add(v___x_587_, v___x_588_);
lean_dec(v___x_588_);
lean_dec(v___x_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* v_word_590_, lean_object* v_patternIdx_591_, lean_object* v_wordIdx_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(v_word_590_, v_patternIdx_591_, v_wordIdx_592_);
lean_dec(v_wordIdx_592_);
lean_dec(v_patternIdx_591_);
lean_dec_ref(v_word_590_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* v_word_594_, lean_object* v_patternIdx_595_, lean_object* v_wordIdx_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_string_length(v_word_594_);
v___x_598_ = lean_nat_mul(v_patternIdx_595_, v___x_597_);
v___x_599_ = lean_nat_add(v___x_598_, v_wordIdx_596_);
lean_dec(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* v_word_600_, lean_object* v_patternIdx_601_, lean_object* v_wordIdx_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(v_word_600_, v_patternIdx_601_, v_wordIdx_602_);
lean_dec(v_wordIdx_602_);
lean_dec(v_patternIdx_601_);
lean_dec_ref(v_word_600_);
return v_res_603_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* v_word_604_, lean_object* v_result_605_, lean_object* v_patternIdx_606_, lean_object* v_wordIdx_607_){
_start:
{
uint16_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint16_t v___x_617_; 
v___x_608_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_609_ = lean_string_length(v_word_604_);
v___x_610_ = lean_nat_mul(v_patternIdx_606_, v___x_609_);
v___x_611_ = lean_unsigned_to_nat(2u);
v___x_612_ = lean_nat_mul(v___x_610_, v___x_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_nat_mul(v_wordIdx_607_, v___x_611_);
v___x_614_ = lean_nat_add(v___x_612_, v___x_613_);
lean_dec(v___x_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(v___x_608_);
v___x_616_ = lean_array_get(v___x_615_, v_result_605_, v___x_614_);
lean_dec(v___x_614_);
lean_dec(v___x_615_);
v___x_617_ = lean_unbox(v___x_616_);
lean_dec(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* v_word_618_, lean_object* v_result_619_, lean_object* v_patternIdx_620_, lean_object* v_wordIdx_621_){
_start:
{
uint16_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_618_, v_result_619_, v_patternIdx_620_, v_wordIdx_621_);
lean_dec(v_wordIdx_621_);
lean_dec(v_patternIdx_620_);
lean_dec_ref(v_result_619_);
lean_dec_ref(v_word_618_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* v_word_624_, lean_object* v_result_625_, lean_object* v_patternIdx_626_, lean_object* v_wordIdx_627_){
_start:
{
uint16_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint16_t v___x_639_; 
v___x_628_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_629_ = lean_string_length(v_word_624_);
v___x_630_ = lean_nat_mul(v_patternIdx_626_, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(2u);
v___x_632_ = lean_nat_mul(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_nat_mul(v_wordIdx_627_, v___x_631_);
v___x_634_ = lean_nat_add(v___x_632_, v___x_633_);
lean_dec(v___x_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v___x_634_, v___x_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(v___x_628_);
v___x_638_ = lean_array_get(v___x_637_, v_result_625_, v___x_636_);
lean_dec(v___x_636_);
lean_dec(v___x_637_);
v___x_639_ = lean_unbox(v___x_638_);
lean_dec(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* v_word_640_, lean_object* v_result_641_, lean_object* v_patternIdx_642_, lean_object* v_wordIdx_643_){
_start:
{
uint16_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_640_, v_result_641_, v_patternIdx_642_, v_wordIdx_643_);
lean_dec(v_wordIdx_643_);
lean_dec(v_patternIdx_642_);
lean_dec_ref(v_result_641_);
lean_dec_ref(v_word_640_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* v_word_646_, lean_object* v_result_647_, lean_object* v_patternIdx_648_, lean_object* v_wordIdx_649_, uint16_t v_missValue_650_, uint16_t v_matchValue_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_idx_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_652_ = lean_string_length(v_word_646_);
v___x_653_ = lean_nat_mul(v_patternIdx_648_, v___x_652_);
v___x_654_ = lean_unsigned_to_nat(2u);
v___x_655_ = lean_nat_mul(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_nat_mul(v_wordIdx_649_, v___x_654_);
v_idx_657_ = lean_nat_add(v___x_655_, v___x_656_);
lean_dec(v___x_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(v_missValue_650_);
v___x_659_ = lean_array_set(v_result_647_, v_idx_657_, v___x_658_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_idx_657_, v___x_660_);
lean_dec(v_idx_657_);
v___x_662_ = lean_box(v_matchValue_651_);
v___x_663_ = lean_array_set(v___x_659_, v___x_661_, v___x_662_);
lean_dec(v___x_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* v_word_664_, lean_object* v_result_665_, lean_object* v_patternIdx_666_, lean_object* v_wordIdx_667_, lean_object* v_missValue_668_, lean_object* v_matchValue_669_){
_start:
{
uint16_t v_missValue_boxed_670_; uint16_t v_matchValue_boxed_671_; lean_object* v_res_672_; 
v_missValue_boxed_670_ = lean_unbox(v_missValue_668_);
v_matchValue_boxed_671_ = lean_unbox(v_matchValue_669_);
v_res_672_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_664_, v_result_665_, v_patternIdx_666_, v_wordIdx_667_, v_missValue_boxed_670_, v_matchValue_boxed_671_);
lean_dec(v_wordIdx_667_);
lean_dec(v_patternIdx_666_);
lean_dec_ref(v_word_664_);
return v_res_672_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0(void){
_start:
{
lean_object* v___x_673_; uint16_t v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_int16_of_nat(v___x_673_);
return v___x_674_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1(void){
_start:
{
lean_object* v___x_675_; uint16_t v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(3u);
v___x_676_ = lean_int16_of_nat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t v_wordRole_677_, uint8_t v_wordStart_678_){
_start:
{
if (v_wordStart_678_ == 0)
{
if (v_wordRole_677_ == 0)
{
uint16_t v___x_679_; 
v___x_679_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
return v___x_679_;
}
else
{
uint16_t v___x_680_; 
v___x_680_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_680_;
}
}
else
{
uint16_t v___x_681_; 
v___x_681_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* v_wordRole_682_, lean_object* v_wordStart_683_){
_start:
{
uint8_t v_wordRole_boxed_684_; uint8_t v_wordStart_boxed_685_; uint16_t v_res_686_; lean_object* v_r_687_; 
v_wordRole_boxed_684_ = lean_unbox(v_wordRole_682_);
v_wordStart_boxed_685_ = lean_unbox(v_wordStart_683_);
v_res_686_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_boxed_684_, v_wordStart_boxed_685_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t v_patternChar_688_, uint32_t v_wordChar_689_, uint8_t v_patternRole_690_, uint8_t v_wordRole_691_){
_start:
{
uint32_t v___y_693_; uint32_t v___y_694_; uint32_t v___y_698_; uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 65;
v___x_706_ = lean_uint32_dec_le(v___x_705_, v_patternChar_688_);
if (v___x_706_ == 0)
{
v___y_698_ = v_patternChar_688_;
goto v___jp_697_;
}
else
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 90;
v___x_708_ = lean_uint32_dec_le(v_patternChar_688_, v___x_707_);
if (v___x_708_ == 0)
{
v___y_698_ = v_patternChar_688_;
goto v___jp_697_;
}
else
{
uint32_t v___x_709_; uint32_t v___x_710_; 
v___x_709_ = 32;
v___x_710_ = lean_uint32_add(v_patternChar_688_, v___x_709_);
v___y_698_ = v___x_710_;
goto v___jp_697_;
}
}
v___jp_692_:
{
uint8_t v___x_695_; 
v___x_695_ = lean_uint32_dec_eq(v___y_693_, v___y_694_);
if (v___x_695_ == 0)
{
return v___x_695_;
}
else
{
if (v_patternRole_690_ == 0)
{
if (v_wordRole_691_ == 0)
{
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
else
{
return v___x_695_;
}
}
}
v___jp_697_:
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 65;
v___x_700_ = lean_uint32_dec_le(v___x_699_, v_wordChar_689_);
if (v___x_700_ == 0)
{
v___y_693_ = v___y_698_;
v___y_694_ = v_wordChar_689_;
goto v___jp_692_;
}
else
{
uint32_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = 90;
v___x_702_ = lean_uint32_dec_le(v_wordChar_689_, v___x_701_);
if (v___x_702_ == 0)
{
v___y_693_ = v___y_698_;
v___y_694_ = v_wordChar_689_;
goto v___jp_692_;
}
else
{
uint32_t v___x_703_; uint32_t v___x_704_; 
v___x_703_ = 32;
v___x_704_ = lean_uint32_add(v_wordChar_689_, v___x_703_);
v___y_693_ = v___y_698_;
v___y_694_ = v___x_704_;
goto v___jp_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object* v_patternChar_711_, lean_object* v_wordChar_712_, lean_object* v_patternRole_713_, lean_object* v_wordRole_714_){
_start:
{
uint32_t v_patternChar_boxed_715_; uint32_t v_wordChar_boxed_716_; uint8_t v_patternRole_boxed_717_; uint8_t v_wordRole_boxed_718_; uint8_t v_res_719_; lean_object* v_r_720_; 
v_patternChar_boxed_715_ = lean_unbox_uint32(v_patternChar_711_);
lean_dec(v_patternChar_711_);
v_wordChar_boxed_716_ = lean_unbox_uint32(v_wordChar_712_);
lean_dec(v_wordChar_712_);
v_patternRole_boxed_717_ = lean_unbox(v_patternRole_713_);
v_wordRole_boxed_718_ = lean_unbox(v_wordRole_714_);
v_res_719_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v_patternChar_boxed_715_, v_wordChar_boxed_716_, v_patternRole_boxed_717_, v_wordRole_boxed_718_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0(void){
_start:
{
lean_object* v___x_721_; uint16_t v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(2u);
v___x_722_ = lean_int16_of_nat(v___x_721_);
return v___x_722_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1(void){
_start:
{
uint16_t v_score_723_; uint16_t v_score_724_; 
v_score_723_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v_score_724_ = lean_int16_add(v_score_723_, v_score_723_);
return v_score_724_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object* v_pattern_725_, lean_object* v_word_726_, lean_object* v_patternIdx_727_, lean_object* v_wordIdx_728_, uint8_t v_patternRole_729_, uint8_t v_wordRole_730_, uint16_t v_consecutive_731_){
_start:
{
uint16_t v_score_733_; uint16_t v_score_738_; uint16_t v___y_744_; uint8_t v___y_745_; lean_object* v___x_748_; uint16_t v_score_750_; uint16_t v_score_757_; uint8_t v___y_761_; uint32_t v___x_762_; uint32_t v___x_763_; uint8_t v___x_764_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v_score_757_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_762_ = lean_string_utf8_get(v_pattern_725_, v_patternIdx_727_);
v___x_763_ = lean_string_utf8_get(v_word_726_, v_wordIdx_728_);
v___x_764_ = lean_uint32_dec_eq(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
if (v_patternRole_729_ == 0)
{
if (v_wordRole_730_ == 0)
{
goto v___jp_758_;
}
else
{
v___y_761_ = v___x_764_;
goto v___jp_760_;
}
}
else
{
v___y_761_ = v___x_764_;
goto v___jp_760_;
}
}
else
{
v___y_761_ = v___x_764_;
goto v___jp_760_;
}
v___jp_732_:
{
uint16_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_735_ = lean_int16_dec_le(v_consecutive_731_, v___x_734_);
if (v___x_735_ == 0)
{
uint16_t v_score_736_; 
v_score_736_ = lean_int16_add(v_score_733_, v_consecutive_731_);
return v_score_736_;
}
else
{
return v_score_733_;
}
}
v___jp_737_:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_nat_dec_eq(v_wordIdx_728_, v___x_739_);
if (v___x_740_ == 0)
{
v_score_733_ = v_score_738_;
goto v___jp_732_;
}
else
{
uint16_t v___x_741_; uint16_t v_score_742_; 
v___x_741_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
v_score_742_ = lean_int16_add(v_score_738_, v___x_741_);
v_score_733_ = v_score_742_;
goto v___jp_732_;
}
}
v___jp_743_:
{
if (v___y_745_ == 0)
{
v_score_738_ = v___y_744_;
goto v___jp_737_;
}
else
{
uint16_t v___x_746_; uint16_t v_score_747_; 
v___x_746_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
v_score_747_ = lean_int16_add(v___y_744_, v___x_746_);
v_score_738_ = v_score_747_;
goto v___jp_737_;
}
}
v___jp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_string_length(v_word_726_);
v___x_752_ = lean_nat_sub(v___x_751_, v___x_748_);
v___x_753_ = lean_nat_dec_eq(v_wordIdx_728_, v___x_752_);
lean_dec(v___x_752_);
if (v___x_753_ == 0)
{
v___y_744_ = v_score_750_;
v___y_745_ = v___x_753_;
goto v___jp_743_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_string_length(v_pattern_725_);
v___x_755_ = lean_nat_sub(v___x_754_, v___x_748_);
v___x_756_ = lean_nat_dec_eq(v_patternIdx_727_, v___x_755_);
lean_dec(v___x_755_);
v___y_744_ = v_score_750_;
v___y_745_ = v___x_756_;
goto v___jp_743_;
}
}
v___jp_758_:
{
uint16_t v_score_759_; 
v_score_759_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
v_score_750_ = v_score_759_;
goto v___jp_749_;
}
v___jp_760_:
{
if (v___y_761_ == 0)
{
v_score_750_ = v_score_757_;
goto v___jp_749_;
}
else
{
goto v___jp_758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* v_pattern_765_, lean_object* v_word_766_, lean_object* v_patternIdx_767_, lean_object* v_wordIdx_768_, lean_object* v_patternRole_769_, lean_object* v_wordRole_770_, lean_object* v_consecutive_771_){
_start:
{
uint8_t v_patternRole_boxed_772_; uint8_t v_wordRole_boxed_773_; uint16_t v_consecutive_boxed_774_; uint16_t v_res_775_; lean_object* v_r_776_; 
v_patternRole_boxed_772_ = lean_unbox(v_patternRole_769_);
v_wordRole_boxed_773_ = lean_unbox(v_wordRole_770_);
v_consecutive_boxed_774_ = lean_unbox(v_consecutive_771_);
v_res_775_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_765_, v_word_766_, v_patternIdx_767_, v_wordIdx_768_, v_patternRole_boxed_772_, v_wordRole_boxed_773_, v_consecutive_boxed_774_);
lean_dec(v_wordIdx_768_);
lean_dec(v_patternIdx_767_);
lean_dec_ref(v_word_766_);
lean_dec_ref(v_pattern_765_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* v_msg_777_){
_start:
{
uint16_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint16_t v___x_781_; 
v___x_778_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_779_ = lean_box(v___x_778_);
v___x_780_ = lean_panic_fn_borrowed(v___x_779_, v_msg_777_);
lean_dec(v___x_779_);
v___x_781_ = lean_unbox(v___x_780_);
lean_dec(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* v_msg_782_){
_start:
{
uint16_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* v___x_785_, lean_object* v_a_786_, uint16_t v_x_787_){
_start:
{
uint16_t v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_789_ = lean_int16_dec_le(v_x_787_, v___x_788_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v___x_785_, v_a_786_);
if (v___x_790_ == 0)
{
return v_x_787_;
}
else
{
uint16_t v___x_791_; uint16_t v___x_792_; 
v___x_791_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_792_ = lean_int16_add(v_x_787_, v___x_791_);
return v___x_792_;
}
}
else
{
return v_x_787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* v___x_793_, lean_object* v_a_794_, lean_object* v_x_795_){
_start:
{
uint16_t v_x_boxed_796_; uint16_t v_res_797_; lean_object* v_r_798_; 
v_x_boxed_796_ = lean_unbox(v_x_795_);
v_res_797_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_793_, v_a_794_, v_x_boxed_796_);
lean_dec(v_a_794_);
lean_dec(v___x_793_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* v_pattern_799_, lean_object* v_word_800_, lean_object* v_a_801_, lean_object* v_a_802_, uint8_t v___x_803_, uint8_t v___x_804_, lean_object* v___x_805_, uint16_t v_x_806_){
_start:
{
uint16_t v_matchScore_807_; uint8_t v___x_808_; 
v_matchScore_807_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_808_ = lean_int16_dec_le(v_x_806_, v_matchScore_807_);
if (v___x_808_ == 0)
{
uint16_t v___x_809_; uint16_t v___x_810_; uint16_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint16_t v___x_814_; uint16_t v___x_815_; 
v___x_809_ = l_instInhabitedInt16;
v___x_810_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_799_, v_word_800_, v_a_801_, v_a_802_, v___x_803_, v___x_804_, v_matchScore_807_);
v___x_811_ = lean_int16_add(v_x_806_, v___x_810_);
v___x_812_ = lean_box(v___x_809_);
v___x_813_ = lean_array_get(v___x_812_, v___x_805_, v_a_802_);
lean_dec(v___x_812_);
v___x_814_ = lean_unbox(v___x_813_);
lean_dec(v___x_813_);
v___x_815_ = lean_int16_sub(v___x_811_, v___x_814_);
return v___x_815_;
}
else
{
return v_x_806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* v_pattern_816_, lean_object* v_word_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_x_823_){
_start:
{
uint8_t v___x_3257__boxed_824_; uint8_t v___x_3258__boxed_825_; uint16_t v_x_boxed_826_; uint16_t v_res_827_; lean_object* v_r_828_; 
v___x_3257__boxed_824_ = lean_unbox(v___x_820_);
v___x_3258__boxed_825_ = lean_unbox(v___x_821_);
v_x_boxed_826_ = lean_unbox(v_x_823_);
v_res_827_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_816_, v_word_817_, v_a_818_, v_a_819_, v___x_3257__boxed_824_, v___x_3258__boxed_825_, v___x_822_, v_x_boxed_826_);
lean_dec_ref(v___x_822_);
lean_dec(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_word_817_);
lean_dec_ref(v_pattern_816_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* v_pattern_829_, lean_object* v_word_830_, lean_object* v_a_831_, lean_object* v_a_832_, uint8_t v___x_833_, uint8_t v___x_834_, uint16_t v___x_835_, uint16_t v_x_836_){
_start:
{
uint16_t v___y_838_; uint16_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_842_ = lean_int16_dec_le(v_x_836_, v___x_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = lean_int16_dec_eq(v___x_835_, v___x_841_);
if (v___x_843_ == 0)
{
v___y_838_ = v___x_835_;
goto v___jp_837_;
}
else
{
lean_object* v___x_844_; uint16_t v___x_845_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_845_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_844_);
v___y_838_ = v___x_845_;
goto v___jp_837_;
}
}
else
{
return v_x_836_;
}
v___jp_837_:
{
uint16_t v___x_839_; uint16_t v___x_840_; 
v___x_839_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_829_, v_word_830_, v_a_831_, v_a_832_, v___x_833_, v___x_834_, v___y_838_);
v___x_840_ = lean_int16_add(v_x_836_, v___x_839_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* v_pattern_846_, lean_object* v_word_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_x_853_){
_start:
{
uint8_t v___x_3297__boxed_854_; uint8_t v___x_3298__boxed_855_; uint16_t v___x_3299__boxed_856_; uint16_t v_x_boxed_857_; uint16_t v_res_858_; lean_object* v_r_859_; 
v___x_3297__boxed_854_ = lean_unbox(v___x_850_);
v___x_3298__boxed_855_ = lean_unbox(v___x_851_);
v___x_3299__boxed_856_ = lean_unbox(v___x_852_);
v_x_boxed_857_ = lean_unbox(v_x_853_);
v_res_858_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_846_, v_word_847_, v_a_848_, v_a_849_, v___x_3297__boxed_854_, v___x_3298__boxed_855_, v___x_3299__boxed_856_, v_x_boxed_857_);
lean_dec(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_word_847_);
lean_dec_ref(v_pattern_846_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* v_word_860_, lean_object* v_a_861_, lean_object* v_pattern_862_, lean_object* v_patternRoles_863_, lean_object* v_wordRoles_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v_range_867_, lean_object* v_b_868_, lean_object* v_i_869_){
_start:
{
lean_object* v_stop_870_; lean_object* v_step_871_; uint8_t v___x_872_; 
v_stop_870_ = lean_ctor_get(v_range_867_, 1);
v_step_871_ = lean_ctor_get(v_range_867_, 2);
v___x_872_ = lean_nat_dec_lt(v_i_869_, v_stop_870_);
if (v___x_872_ == 0)
{
lean_dec(v_i_869_);
return v_b_868_;
}
else
{
lean_object* v_fst_873_; lean_object* v_snd_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_988_; 
v_fst_873_ = lean_ctor_get(v_b_868_, 0);
v_snd_874_ = lean_ctor_get(v_b_868_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_b_868_);
if (v_isSharedCheck_988_ == 0)
{
v___x_876_ = v_b_868_;
v_isShared_877_ = v_isSharedCheck_988_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_snd_874_);
lean_inc(v_fst_873_);
lean_dec(v_b_868_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_988_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; uint16_t v_matchScore_879_; lean_object* v___x_880_; uint16_t v___y_882_; lean_object* v_runLengths_883_; uint16_t v_matchScore_884_; lean_object* v___y_902_; uint16_t v___y_903_; uint16_t v___y_904_; uint16_t v___y_907_; uint8_t v___x_969_; 
v___x_878_ = 0;
v_matchScore_879_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_dec_le(v___x_880_, v_i_869_);
if (v___x_969_ == 0)
{
v___y_907_ = v_matchScore_879_;
goto v___jp_906_;
}
else
{
lean_object* v___x_970_; uint16_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint16_t v___x_983_; uint16_t v___x_984_; uint8_t v___x_985_; 
v___x_970_ = lean_nat_sub(v_i_869_, v___x_880_);
v___x_971_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_972_ = lean_string_length(v_word_860_);
v___x_973_ = lean_nat_mul(v_a_861_, v___x_972_);
v___x_974_ = lean_unsigned_to_nat(2u);
v___x_975_ = lean_nat_mul(v___x_973_, v___x_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_nat_mul(v___x_970_, v___x_974_);
lean_dec(v___x_970_);
v___x_977_ = lean_nat_add(v___x_975_, v___x_976_);
lean_dec(v___x_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(v___x_971_);
v___x_979_ = lean_array_get(v___x_978_, v_fst_873_, v___x_977_);
lean_dec(v___x_978_);
v___x_980_ = lean_nat_add(v___x_977_, v___x_880_);
lean_dec(v___x_977_);
v___x_981_ = lean_box(v___x_971_);
v___x_982_ = lean_array_get(v___x_981_, v_fst_873_, v___x_980_);
lean_dec(v___x_980_);
lean_dec(v___x_981_);
v___x_983_ = lean_unbox(v___x_979_);
v___x_984_ = lean_unbox(v___x_982_);
v___x_985_ = lean_int16_dec_le(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
uint16_t v___x_986_; 
lean_dec(v___x_982_);
v___x_986_ = lean_unbox(v___x_979_);
lean_dec(v___x_979_);
v___y_907_ = v___x_986_;
goto v___jp_906_;
}
else
{
uint16_t v___x_987_; 
lean_dec(v___x_979_);
v___x_987_ = lean_unbox(v___x_982_);
lean_dec(v___x_982_);
v___y_907_ = v___x_987_;
goto v___jp_906_;
}
}
v___jp_881_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_idx_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_885_ = lean_string_length(v_word_860_);
v___x_886_ = lean_nat_mul(v_a_861_, v___x_885_);
v___x_887_ = lean_unsigned_to_nat(2u);
v___x_888_ = lean_nat_mul(v___x_886_, v___x_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_nat_mul(v_i_869_, v___x_887_);
v_idx_890_ = lean_nat_add(v___x_888_, v___x_889_);
lean_dec(v___x_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(v___y_882_);
v___x_892_ = lean_array_set(v_fst_873_, v_idx_890_, v___x_891_);
v___x_893_ = lean_nat_add(v_idx_890_, v___x_880_);
lean_dec(v_idx_890_);
v___x_894_ = lean_box(v_matchScore_884_);
v___x_895_ = lean_array_set(v___x_892_, v___x_893_, v___x_894_);
lean_dec(v___x_893_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_runLengths_883_);
lean_ctor_set(v___x_876_, 0, v___x_895_);
v___x_897_ = v___x_876_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_runLengths_883_);
v___x_897_ = v_reuseFailAlloc_900_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; 
v___x_898_ = lean_nat_add(v_i_869_, v_step_871_);
lean_dec(v_i_869_);
v_b_868_ = v___x_897_;
v_i_869_ = v___x_898_;
goto _start;
}
}
v___jp_901_:
{
uint16_t v___x_905_; 
v___x_905_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_866_, v_i_869_, v___y_904_);
v___y_882_ = v___y_903_;
v_runLengths_883_ = v___y_902_;
v_matchScore_884_ = v___x_905_;
goto v___jp_881_;
}
v___jp_906_:
{
uint32_t v___x_908_; uint32_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; uint8_t v___x_915_; uint8_t v___x_916_; 
v___x_908_ = lean_string_utf8_get(v_pattern_862_, v_a_861_);
v___x_909_ = lean_string_utf8_get(v_word_860_, v_i_869_);
v___x_910_ = lean_box(v___x_878_);
v___x_911_ = lean_array_get(v___x_910_, v_patternRoles_863_, v_a_861_);
lean_dec(v___x_910_);
v___x_912_ = lean_box(v___x_878_);
v___x_913_ = lean_array_get(v___x_912_, v_wordRoles_864_, v_i_869_);
lean_dec(v___x_912_);
v___x_914_ = lean_unbox(v___x_911_);
v___x_915_ = lean_unbox(v___x_913_);
v___x_916_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_908_, v___x_909_, v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v___x_913_);
lean_dec(v___x_911_);
v___y_882_ = v___y_907_;
v_runLengths_883_ = v_snd_874_;
v_matchScore_884_ = v_matchScore_879_;
goto v___jp_881_;
}
else
{
uint8_t v___x_917_; 
v___x_917_ = lean_nat_dec_le(v___x_880_, v_a_861_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint16_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; uint8_t v___x_925_; uint16_t v___x_926_; uint16_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint16_t v___x_930_; uint16_t v___x_931_; uint8_t v___x_932_; 
v___x_918_ = lean_string_length(v_word_860_);
v___x_919_ = lean_nat_mul(v_a_861_, v___x_918_);
v___x_920_ = lean_nat_add(v___x_919_, v_i_869_);
lean_dec(v___x_919_);
v___x_921_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_922_ = lean_box(v___x_921_);
v___x_923_ = lean_array_set(v_snd_874_, v___x_920_, v___x_922_);
lean_dec(v___x_920_);
v___x_924_ = lean_unbox(v___x_911_);
lean_dec(v___x_911_);
v___x_925_ = lean_unbox(v___x_913_);
lean_dec(v___x_913_);
v___x_926_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_862_, v_word_860_, v_a_861_, v_i_869_, v___x_924_, v___x_925_, v_matchScore_879_);
v___x_927_ = l_instInhabitedInt16;
v___x_928_ = lean_box(v___x_927_);
v___x_929_ = lean_array_get(v___x_928_, v___x_865_, v_i_869_);
lean_dec(v___x_928_);
v___x_930_ = lean_unbox(v___x_929_);
lean_dec(v___x_929_);
v___x_931_ = lean_int16_sub(v___x_926_, v___x_930_);
v___x_932_ = lean_int16_dec_eq(v___x_931_, v_matchScore_879_);
if (v___x_932_ == 0)
{
v___y_882_ = v___y_907_;
v_runLengths_883_ = v___x_923_;
v_matchScore_884_ = v___x_931_;
goto v___jp_881_;
}
else
{
lean_object* v___x_933_; uint16_t v___x_934_; 
v___x_933_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_934_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_933_);
v___y_882_ = v___y_907_;
v_runLengths_883_ = v___x_923_;
v_matchScore_884_ = v___x_934_;
goto v___jp_881_;
}
}
else
{
uint16_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint16_t v___x_943_; uint16_t v___x_944_; uint16_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint16_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; uint8_t v___x_958_; uint16_t v___x_959_; uint16_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; uint8_t v___x_965_; uint16_t v___x_966_; uint16_t v___x_967_; uint8_t v___x_968_; 
v___x_935_ = l_instInhabitedInt16;
v___x_936_ = lean_nat_sub(v_a_861_, v___x_880_);
v___x_937_ = lean_nat_sub(v_i_869_, v___x_880_);
v___x_938_ = lean_string_length(v_word_860_);
v___x_939_ = lean_nat_mul(v___x_936_, v___x_938_);
lean_dec(v___x_936_);
v___x_940_ = lean_nat_add(v___x_939_, v___x_937_);
v___x_941_ = lean_box(v___x_935_);
v___x_942_ = lean_array_get(v___x_941_, v_snd_874_, v___x_940_);
lean_dec(v___x_940_);
lean_dec(v___x_941_);
v___x_943_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_944_ = lean_unbox(v___x_942_);
lean_dec(v___x_942_);
v___x_945_ = lean_int16_add(v___x_944_, v___x_943_);
v___x_946_ = lean_nat_mul(v_a_861_, v___x_938_);
v___x_947_ = lean_nat_add(v___x_946_, v_i_869_);
lean_dec(v___x_946_);
v___x_948_ = lean_box(v___x_945_);
v___x_949_ = lean_array_set(v_snd_874_, v___x_947_, v___x_948_);
lean_dec(v___x_947_);
v___x_950_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_951_ = lean_unsigned_to_nat(2u);
v___x_952_ = lean_nat_mul(v___x_939_, v___x_951_);
lean_dec(v___x_939_);
v___x_953_ = lean_nat_mul(v___x_937_, v___x_951_);
lean_dec(v___x_937_);
v___x_954_ = lean_nat_add(v___x_952_, v___x_953_);
lean_dec(v___x_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(v___x_950_);
v___x_956_ = lean_array_get(v___x_955_, v_fst_873_, v___x_954_);
lean_dec(v___x_955_);
v___x_957_ = lean_unbox(v___x_911_);
v___x_958_ = lean_unbox(v___x_913_);
v___x_959_ = lean_unbox(v___x_956_);
lean_dec(v___x_956_);
v___x_960_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_862_, v_word_860_, v_a_861_, v_i_869_, v___x_957_, v___x_958_, v___x_865_, v___x_959_);
v___x_961_ = lean_nat_add(v___x_954_, v___x_880_);
lean_dec(v___x_954_);
v___x_962_ = lean_box(v___x_950_);
v___x_963_ = lean_array_get(v___x_962_, v_fst_873_, v___x_961_);
lean_dec(v___x_961_);
lean_dec(v___x_962_);
v___x_964_ = lean_unbox(v___x_911_);
lean_dec(v___x_911_);
v___x_965_ = lean_unbox(v___x_913_);
lean_dec(v___x_913_);
v___x_966_ = lean_unbox(v___x_963_);
lean_dec(v___x_963_);
v___x_967_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_862_, v_word_860_, v_a_861_, v_i_869_, v___x_964_, v___x_965_, v___x_945_, v___x_966_);
v___x_968_ = lean_int16_dec_le(v___x_960_, v___x_967_);
if (v___x_968_ == 0)
{
v___y_902_ = v___x_949_;
v___y_903_ = v___y_907_;
v___y_904_ = v___x_960_;
goto v___jp_901_;
}
else
{
v___y_902_ = v___x_949_;
v___y_903_ = v___y_907_;
v___y_904_ = v___x_967_;
goto v___jp_901_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* v_word_989_, lean_object* v_a_990_, lean_object* v_pattern_991_, lean_object* v_patternRoles_992_, lean_object* v_wordRoles_993_, lean_object* v___x_994_, lean_object* v___x_995_, lean_object* v_range_996_, lean_object* v_b_997_, lean_object* v_i_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_989_, v_a_990_, v_pattern_991_, v_patternRoles_992_, v_wordRoles_993_, v___x_994_, v___x_995_, v_range_996_, v_b_997_, v_i_998_);
lean_dec_ref(v_range_996_);
lean_dec(v___x_995_);
lean_dec_ref(v___x_994_);
lean_dec_ref(v_wordRoles_993_);
lean_dec_ref(v_patternRoles_992_);
lean_dec_ref(v_pattern_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_word_989_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v_word_1002_, lean_object* v_pattern_1003_, lean_object* v_patternRoles_1004_, lean_object* v_wordRoles_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v_range_1008_, lean_object* v_b_1009_, lean_object* v_i_1010_){
_start:
{
lean_object* v_stop_1011_; lean_object* v_step_1012_; uint8_t v___x_1013_; 
v_stop_1011_ = lean_ctor_get(v_range_1008_, 1);
v_step_1012_ = lean_ctor_get(v_range_1008_, 2);
v___x_1013_ = lean_nat_dec_lt(v_i_1010_, v_stop_1011_);
if (v___x_1013_ == 0)
{
lean_dec(v_i_1010_);
return v_b_1009_;
}
else
{
lean_object* v_fst_1014_; lean_object* v_snd_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1039_; 
v_fst_1014_ = lean_ctor_get(v_b_1009_, 0);
v_snd_1015_ = lean_ctor_get(v_b_1009_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_b_1009_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1017_ = v_b_1009_;
v_isShared_1018_ = v_isSharedCheck_1039_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_snd_1015_);
lean_inc(v_fst_1014_);
lean_dec(v_b_1009_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1039_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_sub(v___x_1000_, v_i_1010_);
v___x_1021_ = lean_nat_sub(v___x_1020_, v___x_1019_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_nat_sub(v___x_1001_, v___x_1021_);
lean_dec(v___x_1021_);
lean_inc(v_i_1010_);
v___x_1023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1023_, 0, v_i_1010_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
lean_ctor_set(v___x_1023_, 2, v___x_1019_);
if (v_isShared_1018_ == 0)
{
v___x_1025_ = v___x_1017_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_fst_1014_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_snd_1015_);
v___x_1025_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1037_; 
lean_inc(v_i_1010_);
v___x_1026_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1002_, v_i_1010_, v_pattern_1003_, v_patternRoles_1004_, v_wordRoles_1005_, v___x_1006_, v___x_1007_, v___x_1023_, v___x_1025_, v_i_1010_);
lean_dec_ref_known(v___x_1023_, 3);
v_fst_1027_ = lean_ctor_get(v___x_1026_, 0);
v_snd_1028_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1030_ = v___x_1026_;
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v___x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_fst_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_snd_1028_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_nat_add(v_i_1010_, v_step_1012_);
lean_dec(v_i_1010_);
v_b_1009_ = v___x_1033_;
v_i_1010_ = v___x_1034_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v_word_1042_, lean_object* v_pattern_1043_, lean_object* v_patternRoles_1044_, lean_object* v_wordRoles_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v_range_1048_, lean_object* v_b_1049_, lean_object* v_i_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1040_, v___x_1041_, v_word_1042_, v_pattern_1043_, v_patternRoles_1044_, v_wordRoles_1045_, v___x_1046_, v___x_1047_, v_range_1048_, v_b_1049_, v_i_1050_);
lean_dec_ref(v_range_1048_);
lean_dec(v___x_1047_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_wordRoles_1045_);
lean_dec_ref(v_patternRoles_1044_);
lean_dec_ref(v_pattern_1043_);
lean_dec_ref(v_word_1042_);
lean_dec(v___x_1041_);
lean_dec(v___x_1040_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* v_word_1052_, lean_object* v_pattern_1053_, lean_object* v_patternRoles_1054_, lean_object* v_wordRoles_1055_, lean_object* v___x_1056_, lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v___x_1059_, lean_object* v_range_1060_, lean_object* v_b_1061_, lean_object* v_i_1062_){
_start:
{
lean_object* v_stop_1063_; lean_object* v_step_1064_; uint8_t v___x_1065_; 
v_stop_1063_ = lean_ctor_get(v_range_1060_, 1);
v_step_1064_ = lean_ctor_get(v_range_1060_, 2);
v___x_1065_ = lean_nat_dec_lt(v_i_1062_, v_stop_1063_);
if (v___x_1065_ == 0)
{
lean_dec(v_i_1062_);
return v_b_1061_;
}
else
{
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1091_; 
v_fst_1066_ = lean_ctor_get(v_b_1061_, 0);
v_snd_1067_ = lean_ctor_get(v_b_1061_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_b_1061_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1069_ = v_b_1061_;
v_isShared_1070_ = v_isSharedCheck_1091_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1066_);
lean_dec(v_b_1061_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1091_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_sub(v___x_1058_, v_i_1062_);
v___x_1073_ = lean_nat_sub(v___x_1072_, v___x_1071_);
lean_dec(v___x_1072_);
v___x_1074_ = lean_nat_sub(v___x_1059_, v___x_1073_);
lean_dec(v___x_1073_);
lean_inc(v_i_1062_);
v___x_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1075_, 0, v_i_1062_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_ctor_set(v___x_1075_, 2, v___x_1071_);
if (v_isShared_1070_ == 0)
{
v___x_1077_ = v___x_1069_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_fst_1066_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1067_);
v___x_1077_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
lean_inc(v_i_1062_);
v___x_1078_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1052_, v_i_1062_, v_pattern_1053_, v_patternRoles_1054_, v_wordRoles_1055_, v___x_1056_, v___x_1057_, v___x_1075_, v___x_1077_, v_i_1062_);
lean_dec_ref_known(v___x_1075_, 3);
v_fst_1079_ = lean_ctor_get(v___x_1078_, 0);
v_snd_1080_ = lean_ctor_get(v___x_1078_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_inc(v_fst_1079_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_fst_1079_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_snd_1080_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_nat_add(v_i_1062_, v_step_1064_);
lean_dec(v_i_1062_);
v___x_1087_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1058_, v___x_1059_, v_word_1052_, v_pattern_1053_, v_patternRoles_1054_, v_wordRoles_1055_, v___x_1056_, v___x_1057_, v_range_1060_, v___x_1085_, v___x_1086_);
return v___x_1087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* v_word_1092_, lean_object* v_pattern_1093_, lean_object* v_patternRoles_1094_, lean_object* v_wordRoles_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_range_1100_, lean_object* v_b_1101_, lean_object* v_i_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1092_, v_pattern_1093_, v_patternRoles_1094_, v_wordRoles_1095_, v___x_1096_, v___x_1097_, v___x_1098_, v___x_1099_, v_range_1100_, v_b_1101_, v_i_1102_);
lean_dec_ref(v_range_1100_);
lean_dec(v___x_1099_);
lean_dec(v___x_1098_);
lean_dec(v___x_1097_);
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_wordRoles_1095_);
lean_dec_ref(v_patternRoles_1094_);
lean_dec_ref(v_pattern_1093_);
lean_dec_ref(v_word_1092_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* v_wordRoles_1104_, lean_object* v_range_1105_, lean_object* v_b_1106_, lean_object* v_i_1107_){
_start:
{
lean_object* v_stop_1108_; lean_object* v_step_1109_; uint8_t v___x_1110_; 
v_stop_1108_ = lean_ctor_get(v_range_1105_, 1);
v_step_1109_ = lean_ctor_get(v_range_1105_, 2);
v___x_1110_ = lean_nat_dec_lt(v_i_1107_, v_stop_1108_);
if (v___x_1110_ == 0)
{
lean_dec(v_i_1107_);
return v_b_1106_;
}
else
{
lean_object* v_snd_1111_; lean_object* v_snd_1112_; lean_object* v_fst_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1169_; 
v_snd_1111_ = lean_ctor_get(v_b_1106_, 1);
lean_inc(v_snd_1111_);
v_snd_1112_ = lean_ctor_get(v_snd_1111_, 1);
lean_inc(v_snd_1112_);
v_fst_1113_ = lean_ctor_get(v_b_1106_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_b_1106_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_b_1106_, 1);
lean_dec(v_unused_1170_);
v___x_1115_ = v_b_1106_;
v_isShared_1116_ = v_isSharedCheck_1169_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_fst_1113_);
lean_dec(v_b_1106_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1169_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_fst_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1167_; 
v_fst_1117_ = lean_ctor_get(v_snd_1111_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_snd_1111_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v_snd_1111_, 1);
lean_dec(v_unused_1168_);
v___x_1119_ = v_snd_1111_;
v_isShared_1120_ = v_isSharedCheck_1167_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_fst_1117_);
lean_dec(v_snd_1111_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1167_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1166_; 
v_fst_1121_ = lean_ctor_get(v_snd_1112_, 0);
v_snd_1122_ = lean_ctor_get(v_snd_1112_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_snd_1112_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1124_ = v_snd_1112_;
v_isShared_1125_ = v_isSharedCheck_1166_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snd_1122_);
lean_inc(v_fst_1121_);
lean_dec(v_snd_1112_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1166_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
uint8_t v___x_1126_; lean_object* v_lastSepIdx_1127_; lean_object* v_lastSepIdx_1129_; uint16_t v_penaltyNs_1130_; uint16_t v_penaltySkip_1131_; uint8_t v___x_1154_; 
v___x_1126_ = 0;
v_lastSepIdx_1127_ = lean_unsigned_to_nat(0u);
v___x_1154_ = lean_nat_dec_eq(v_i_1107_, v_lastSepIdx_1127_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_box(v___x_1126_);
v___x_1156_ = lean_array_get(v___x_1155_, v_wordRoles_1104_, v_i_1107_);
lean_dec(v___x_1155_);
v___x_1157_ = lean_unbox(v___x_1156_);
lean_dec(v___x_1156_);
if (v___x_1157_ == 2)
{
uint16_t v_penaltyNs_1158_; uint16_t v___x_1159_; uint16_t v___x_1160_; uint16_t v___x_1161_; 
lean_dec(v_snd_1122_);
lean_dec(v_fst_1117_);
v_penaltyNs_1158_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1159_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1160_ = lean_unbox(v_fst_1121_);
lean_dec(v_fst_1121_);
v___x_1161_ = lean_int16_add(v___x_1160_, v___x_1159_);
lean_inc(v_i_1107_);
v_lastSepIdx_1129_ = v_i_1107_;
v_penaltyNs_1130_ = v___x_1161_;
v_penaltySkip_1131_ = v_penaltyNs_1158_;
goto v___jp_1128_;
}
else
{
uint16_t v___x_1162_; uint16_t v___x_1163_; 
v___x_1162_ = lean_unbox(v_fst_1121_);
lean_dec(v_fst_1121_);
v___x_1163_ = lean_unbox(v_snd_1122_);
lean_dec(v_snd_1122_);
v_lastSepIdx_1129_ = v_fst_1117_;
v_penaltyNs_1130_ = v___x_1162_;
v_penaltySkip_1131_ = v___x_1163_;
goto v___jp_1128_;
}
}
else
{
uint16_t v___x_1164_; uint16_t v___x_1165_; 
v___x_1164_ = lean_unbox(v_fst_1121_);
lean_dec(v_fst_1121_);
v___x_1165_ = lean_unbox(v_snd_1122_);
lean_dec(v_snd_1122_);
v_lastSepIdx_1129_ = v_fst_1117_;
v_penaltyNs_1130_ = v___x_1164_;
v_penaltySkip_1131_ = v___x_1165_;
goto v___jp_1128_;
}
v___jp_1128_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; uint8_t v___x_1135_; uint16_t v___x_1136_; uint16_t v___x_1137_; uint16_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1132_ = lean_box(v___x_1126_);
v___x_1133_ = lean_array_get(v___x_1132_, v_wordRoles_1104_, v_i_1107_);
lean_dec(v___x_1132_);
v___x_1134_ = lean_nat_dec_eq(v_i_1107_, v_lastSepIdx_1127_);
v___x_1135_ = lean_unbox(v___x_1133_);
lean_dec(v___x_1133_);
v___x_1136_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_1135_, v___x_1134_);
v___x_1137_ = lean_int16_add(v_penaltySkip_1131_, v___x_1136_);
v___x_1138_ = lean_int16_add(v___x_1137_, v_penaltyNs_1130_);
v___x_1139_ = lean_box(v___x_1138_);
v___x_1140_ = lean_array_set(v_fst_1113_, v_i_1107_, v___x_1139_);
v___x_1141_ = lean_box(v_penaltyNs_1130_);
v___x_1142_ = lean_box(v___x_1137_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___x_1142_);
lean_ctor_set(v___x_1124_, 0, v___x_1141_);
v___x_1144_ = v___x_1124_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v___x_1144_);
lean_ctor_set(v___x_1119_, 0, v_lastSepIdx_1129_);
v___x_1146_ = v___x_1119_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_lastSepIdx_1129_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v___x_1146_);
lean_ctor_set(v___x_1115_, 0, v___x_1140_);
v___x_1148_ = v___x_1115_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_nat_add(v_i_1107_, v_step_1109_);
lean_dec(v_i_1107_);
v_b_1106_ = v___x_1148_;
v_i_1107_ = v___x_1149_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* v_wordRoles_1171_, lean_object* v_range_1172_, lean_object* v_b_1173_, lean_object* v_i_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1171_, v_range_1172_, v_b_1173_, v_i_1174_);
lean_dec_ref(v_range_1172_);
lean_dec_ref(v_wordRoles_1171_);
return v_res_1175_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0(void){
_start:
{
uint16_t v_penaltyNs_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_penaltyNs_1176_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1177_ = lean_box(v_penaltyNs_1176_);
v___x_1178_ = lean_box(v_penaltyNs_1176_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1(void){
_start:
{
lean_object* v___x_1180_; lean_object* v_lastSepIdx_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
v_lastSepIdx_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_lastSepIdx_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* v_pattern_1183_, lean_object* v_word_1184_, lean_object* v_patternRoles_1185_, lean_object* v_wordRoles_1186_){
_start:
{
uint16_t v___y_1188_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_lastSepIdx_1199_; uint16_t v_penaltyNs_1200_; lean_object* v___x_1201_; lean_object* v_runLengths_1202_; lean_object* v___x_1203_; lean_object* v_startPenalties_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_snd_1210_; lean_object* v_fst_1211_; lean_object* v_fst_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1242_; 
v___x_1194_ = lean_string_length(v_pattern_1183_);
v___x_1195_ = lean_string_length(v_word_1184_);
v___x_1196_ = lean_nat_mul(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(2u);
v___x_1198_ = lean_nat_mul(v___x_1196_, v___x_1197_);
v_lastSepIdx_1199_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1200_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1201_ = lean_box(v_penaltyNs_1200_);
v_runLengths_1202_ = lean_mk_array(v___x_1196_, v___x_1201_);
v___x_1203_ = lean_box(v_penaltyNs_1200_);
v_startPenalties_1204_ = lean_mk_array(v___x_1195_, v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1206_, 0, v_lastSepIdx_1199_);
lean_ctor_set(v___x_1206_, 1, v___x_1195_);
lean_ctor_set(v___x_1206_, 2, v___x_1205_);
v___x_1207_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_startPenalties_1204_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1186_, v___x_1206_, v___x_1208_, v_lastSepIdx_1199_);
lean_dec_ref_known(v___x_1206_, 3);
v_snd_1210_ = lean_ctor_get(v___x_1209_, 1);
lean_inc(v_snd_1210_);
v_fst_1211_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_fst_1211_);
lean_dec_ref(v___x_1209_);
v_fst_1212_ = lean_ctor_get(v_snd_1210_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_snd_1210_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_snd_1210_, 1);
lean_dec(v_unused_1243_);
v___x_1214_ = v_snd_1210_;
v_isShared_1215_ = v_isSharedCheck_1242_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_fst_1212_);
lean_dec(v_snd_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1242_;
goto v_resetjp_1213_;
}
v___jp_1187_:
{
uint16_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1190_ = lean_int16_dec_le(v___y_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_int16_to_int(v___y_1188_);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_box(0);
return v___x_1193_;
}
}
v_resetjp_1213_:
{
uint16_t v_matchScore_1216_; lean_object* v___x_1217_; lean_object* v_result_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v_matchScore_1216_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1217_ = lean_box(v_matchScore_1216_);
v_result_1218_ = lean_mk_array(v___x_1198_, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1219_, 0, v_lastSepIdx_1199_);
lean_ctor_set(v___x_1219_, 1, v___x_1194_);
lean_ctor_set(v___x_1219_, 2, v___x_1205_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v_runLengths_1202_);
lean_ctor_set(v___x_1214_, 0, v_result_1218_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_result_1218_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_runLengths_1202_);
v___x_1221_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v_fst_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint16_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint16_t v___x_1236_; uint16_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1222_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1184_, v_pattern_1183_, v_patternRoles_1185_, v_wordRoles_1186_, v_fst_1211_, v_fst_1212_, v___x_1194_, v___x_1195_, v___x_1219_, v___x_1221_, v_lastSepIdx_1199_);
lean_dec_ref_known(v___x_1219_, 3);
lean_dec(v_fst_1212_);
lean_dec(v_fst_1211_);
v_fst_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_fst_1223_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = lean_nat_sub(v___x_1194_, v___x_1205_);
v___x_1225_ = lean_nat_sub(v___x_1195_, v___x_1205_);
v___x_1226_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1227_ = lean_nat_mul(v___x_1224_, v___x_1195_);
lean_dec(v___x_1224_);
v___x_1228_ = lean_nat_mul(v___x_1227_, v___x_1197_);
lean_dec(v___x_1227_);
v___x_1229_ = lean_nat_mul(v___x_1225_, v___x_1197_);
lean_dec(v___x_1225_);
v___x_1230_ = lean_nat_add(v___x_1228_, v___x_1229_);
lean_dec(v___x_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(v___x_1226_);
v___x_1232_ = lean_array_get(v___x_1231_, v_fst_1223_, v___x_1230_);
lean_dec(v___x_1231_);
v___x_1233_ = lean_nat_add(v___x_1230_, v___x_1205_);
lean_dec(v___x_1230_);
v___x_1234_ = lean_box(v___x_1226_);
v___x_1235_ = lean_array_get(v___x_1234_, v_fst_1223_, v___x_1233_);
lean_dec(v___x_1233_);
lean_dec(v_fst_1223_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_unbox(v___x_1232_);
v___x_1237_ = lean_unbox(v___x_1235_);
v___x_1238_ = lean_int16_dec_le(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
uint16_t v___x_1239_; 
lean_dec(v___x_1235_);
v___x_1239_ = lean_unbox(v___x_1232_);
lean_dec(v___x_1232_);
v___y_1188_ = v___x_1239_;
goto v___jp_1187_;
}
else
{
uint16_t v___x_1240_; 
lean_dec(v___x_1232_);
v___x_1240_ = lean_unbox(v___x_1235_);
lean_dec(v___x_1235_);
v___y_1188_ = v___x_1240_;
goto v___jp_1187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* v_pattern_1244_, lean_object* v_word_1245_, lean_object* v_patternRoles_1246_, lean_object* v_wordRoles_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1244_, v_word_1245_, v_patternRoles_1246_, v_wordRoles_1247_);
lean_dec_ref(v_wordRoles_1247_);
lean_dec_ref(v_patternRoles_1246_);
lean_dec_ref(v_word_1245_);
lean_dec_ref(v_pattern_1244_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* v_wordRoles_1249_, lean_object* v_range_1250_, lean_object* v_b_1251_, lean_object* v_i_1252_, lean_object* v_hs_1253_, lean_object* v_hl_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1249_, v_range_1250_, v_b_1251_, v_i_1252_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* v_wordRoles_1256_, lean_object* v_range_1257_, lean_object* v_b_1258_, lean_object* v_i_1259_, lean_object* v_hs_1260_, lean_object* v_hl_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_1256_, v_range_1257_, v_b_1258_, v_i_1259_, v_hs_1260_, v_hl_1261_);
lean_dec_ref(v_range_1257_);
lean_dec_ref(v_wordRoles_1256_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* v_word_1263_, lean_object* v_a_1264_, lean_object* v_pattern_1265_, lean_object* v_patternRoles_1266_, lean_object* v_wordRoles_1267_, lean_object* v___x_1268_, lean_object* v___x_1269_, lean_object* v_range_1270_, lean_object* v_b_1271_, lean_object* v_i_1272_, lean_object* v_hs_1273_, lean_object* v_hl_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1263_, v_a_1264_, v_pattern_1265_, v_patternRoles_1266_, v_wordRoles_1267_, v___x_1268_, v___x_1269_, v_range_1270_, v_b_1271_, v_i_1272_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* v_word_1276_, lean_object* v_a_1277_, lean_object* v_pattern_1278_, lean_object* v_patternRoles_1279_, lean_object* v_wordRoles_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v_range_1283_, lean_object* v_b_1284_, lean_object* v_i_1285_, lean_object* v_hs_1286_, lean_object* v_hl_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v_word_1276_, v_a_1277_, v_pattern_1278_, v_patternRoles_1279_, v_wordRoles_1280_, v___x_1281_, v___x_1282_, v_range_1283_, v_b_1284_, v_i_1285_, v_hs_1286_, v_hl_1287_);
lean_dec_ref(v_range_1283_);
lean_dec(v___x_1282_);
lean_dec_ref(v___x_1281_);
lean_dec_ref(v_wordRoles_1280_);
lean_dec_ref(v_patternRoles_1279_);
lean_dec_ref(v_pattern_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_word_1276_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* v_word_1289_, lean_object* v_pattern_1290_, lean_object* v_patternRoles_1291_, lean_object* v_wordRoles_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_range_1297_, lean_object* v_b_1298_, lean_object* v_i_1299_, lean_object* v_hs_1300_, lean_object* v_hl_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1289_, v_pattern_1290_, v_patternRoles_1291_, v_wordRoles_1292_, v___x_1293_, v___x_1294_, v___x_1295_, v___x_1296_, v_range_1297_, v_b_1298_, v_i_1299_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* v_word_1303_, lean_object* v_pattern_1304_, lean_object* v_patternRoles_1305_, lean_object* v_wordRoles_1306_, lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v_range_1311_, lean_object* v_b_1312_, lean_object* v_i_1313_, lean_object* v_hs_1314_, lean_object* v_hl_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v_word_1303_, v_pattern_1304_, v_patternRoles_1305_, v_wordRoles_1306_, v___x_1307_, v___x_1308_, v___x_1309_, v___x_1310_, v_range_1311_, v_b_1312_, v_i_1313_, v_hs_1314_, v_hl_1315_);
lean_dec_ref(v_range_1311_);
lean_dec(v___x_1310_);
lean_dec(v___x_1309_);
lean_dec(v___x_1308_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v_wordRoles_1306_);
lean_dec_ref(v_patternRoles_1305_);
lean_dec_ref(v_pattern_1304_);
lean_dec_ref(v_word_1303_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v_word_1319_, lean_object* v_pattern_1320_, lean_object* v_patternRoles_1321_, lean_object* v_wordRoles_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_range_1325_, lean_object* v_b_1326_, lean_object* v_i_1327_, lean_object* v_hs_1328_, lean_object* v_hl_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1317_, v___x_1318_, v_word_1319_, v_pattern_1320_, v_patternRoles_1321_, v_wordRoles_1322_, v___x_1323_, v___x_1324_, v_range_1325_, v_b_1326_, v_i_1327_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object* v___x_1331_, lean_object* v___x_1332_, lean_object* v_word_1333_, lean_object* v_pattern_1334_, lean_object* v_patternRoles_1335_, lean_object* v_wordRoles_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v_range_1339_, lean_object* v_b_1340_, lean_object* v_i_1341_, lean_object* v_hs_1342_, lean_object* v_hl_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(v___x_1331_, v___x_1332_, v_word_1333_, v_pattern_1334_, v_patternRoles_1335_, v_wordRoles_1336_, v___x_1337_, v___x_1338_, v_range_1339_, v_b_1340_, v_i_1341_, v_hs_1342_, v_hl_1343_);
lean_dec_ref(v_range_1339_);
lean_dec(v___x_1338_);
lean_dec_ref(v___x_1337_);
lean_dec_ref(v_wordRoles_1336_);
lean_dec_ref(v_patternRoles_1335_);
lean_dec_ref(v_pattern_1334_);
lean_dec_ref(v_word_1333_);
lean_dec(v___x_1332_);
lean_dec(v___x_1331_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_nat_to_int(v_a_1345_);
return v___x_1346_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1347_; double v___x_1348_; 
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_float_of_nat(v___x_1347_);
return v___x_1348_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1(void){
_start:
{
lean_object* v___x_1349_; double v___x_1350_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_float_of_nat(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_unsigned_to_nat(2u);
v___x_1352_ = lean_nat_to_int(v___x_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1(void){
_start:
{
double v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1354_ = lean_box_float(v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* v_pattern_1357_, lean_object* v_word_1358_){
_start:
{
double v___y_1360_; double v___y_1361_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_string_utf8_byte_size(v_pattern_1357_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_nat_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_score_1373_; uint8_t v___x_1389_; 
v___x_1370_ = lean_string_length(v_word_1358_);
v___x_1371_ = lean_string_length(v_pattern_1357_);
v___x_1389_ = lean_nat_dec_lt(v___x_1370_, v___x_1371_);
if (v___x_1389_ == 0)
{
uint8_t v___x_1390_; 
v___x_1390_ = l_Lean_String_charactersIn(v_pattern_1357_, v_word_1358_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_box(0);
return v___x_1391_;
}
else
{
if (v___x_1369_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_1357_);
v___x_1393_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_1358_);
v___x_1394_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1357_, v_word_1358_, v___x_1392_, v___x_1393_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
if (lean_obj_tag(v___x_1394_) == 1)
{
lean_object* v_val_1395_; uint8_t v___x_1396_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = lean_nat_dec_eq(v___x_1371_, v___x_1370_);
if (v___x_1396_ == 0)
{
v_score_1373_ = v_val_1395_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1397_; lean_object* v_score_1398_; 
v___x_1397_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
v_score_1398_ = lean_int_mul(v_val_1395_, v___x_1397_);
lean_dec(v_val_1395_);
v_score_1373_ = v_score_1398_;
goto v___jp_1372_;
}
}
else
{
lean_object* v___x_1399_; 
lean_dec(v___x_1394_);
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
}
else
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_box(0);
return v___x_1400_;
}
}
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_box(0);
return v___x_1401_;
}
v___jp_1372_:
{
lean_object* v_perfect_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_perfectMatch_1381_; double v___x_1382_; lean_object* v___x_1383_; double v___x_1384_; double v_normScore_1385_; double v___x_1386_; double v___x_1387_; uint8_t v___x_1388_; 
v_perfect_1374_ = lean_unsigned_to_nat(4u);
v___x_1375_ = lean_nat_mul(v_perfect_1374_, v___x_1371_);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v___x_1371_, v___x_1376_);
v___x_1378_ = lean_nat_mul(v___x_1371_, v___x_1377_);
lean_dec(v___x_1377_);
v___x_1379_ = lean_nat_shiftr(v___x_1378_, v___x_1376_);
lean_dec(v___x_1378_);
v___x_1380_ = lean_nat_sub(v___x_1379_, v___x_1376_);
lean_dec(v___x_1379_);
v_perfectMatch_1381_ = lean_nat_add(v___x_1375_, v___x_1380_);
lean_dec(v___x_1380_);
lean_dec(v___x_1375_);
v___x_1382_ = l_Float_ofInt(v_score_1373_);
lean_dec(v_score_1373_);
v___x_1383_ = lean_nat_to_int(v_perfectMatch_1381_);
v___x_1384_ = l_Float_ofInt(v___x_1383_);
lean_dec(v___x_1383_);
v_normScore_1385_ = lean_float_div(v___x_1382_, v___x_1384_);
v___x_1386_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1387_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1);
v___x_1388_ = lean_float_decLe(v___x_1387_, v_normScore_1385_);
if (v___x_1388_ == 0)
{
v___y_1360_ = v___x_1386_;
v___y_1361_ = v___x_1387_;
goto v___jp_1359_;
}
else
{
v___y_1360_ = v___x_1386_;
v___y_1361_ = v_normScore_1385_;
goto v___jp_1359_;
}
}
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return v___x_1402_;
}
v___jp_1359_:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_float_decLe(v___y_1360_, v___y_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_box_float(v___y_1361_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_box_float(v___y_1360_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* v_pattern_1403_, lean_object* v_word_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1403_, v_word_1404_);
lean_dec_ref(v_word_1404_);
lean_dec_ref(v_pattern_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* v_pattern_1406_, lean_object* v_word_1407_, double v_threshold_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1406_, v_word_1407_);
if (lean_obj_tag(v___x_1409_) == 0)
{
return v___x_1409_;
}
else
{
lean_object* v_val_1410_; double v___x_1411_; uint8_t v___x_1412_; 
v_val_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_val_1410_);
v___x_1411_ = lean_unbox_float(v_val_1410_);
lean_dec(v_val_1410_);
v___x_1412_ = lean_float_decLt(v_threshold_1408_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref_known(v___x_1409_, 1);
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* v_pattern_1414_, lean_object* v_word_1415_, lean_object* v_threshold_1416_){
_start:
{
double v_threshold_boxed_1417_; lean_object* v_res_1418_; 
v_threshold_boxed_1417_ = lean_unbox_float(v_threshold_1416_);
lean_dec_ref(v_threshold_1416_);
v_res_1418_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1414_, v_word_1415_, v_threshold_boxed_1417_);
lean_dec_ref(v_word_1415_);
lean_dec_ref(v_pattern_1414_);
return v_res_1418_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* v_pattern_1419_, lean_object* v_word_1420_, double v_threshold_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1419_, v_word_1420_, v_threshold_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = 1;
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* v_pattern_1425_, lean_object* v_word_1426_, lean_object* v_threshold_1427_){
_start:
{
double v_threshold_boxed_1428_; uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_threshold_boxed_1428_ = lean_unbox_float(v_threshold_1427_);
lean_dec_ref(v_threshold_1427_);
v_res_1429_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1425_, v_word_1426_, v_threshold_boxed_1428_);
lean_dec_ref(v_word_1426_);
lean_dec_ref(v_pattern_1425_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_FuzzyMatching(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
