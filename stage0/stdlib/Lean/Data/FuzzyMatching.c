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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9));
v___x_53_ = lean_string_utf8_byte_size(v_string_51_);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_nat_dec_eq(v___x_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_56_ = lean_string_length(v_string_51_);
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_nat_dec_eq(v___x_56_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v_result_59_; lean_object* v___x_60_; uint32_t v___x_61_; uint32_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_result_67_; lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint32_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint32_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_result_59_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_string_utf8_get(v_string_51_, v___x_54_);
v___x_62_ = lean_string_utf8_get(v_string_51_, v___x_57_);
v___x_63_ = lean_box_uint32(v___x_62_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
v___x_65_ = lean_box_uint32(v___x_61_);
lean_inc_n(v_f_50_, 2);
v___x_66_ = lean_apply_3(v_f_50_, v___x_60_, v___x_65_, v___x_64_);
v_result_67_ = lean_array_push(v_result_59_, v___x_66_);
v___x_68_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v_string_51_);
v___f_69_ = lean_alloc_closure((void*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_69_, 0, v___x_68_);
lean_closure_set(v___f_69_, 1, v_string_51_);
lean_closure_set(v___f_69_, 2, v___x_57_);
lean_closure_set(v___f_69_, 3, v_f_50_);
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_56_);
lean_ctor_set(v___x_70_, 2, v___x_57_);
v___x_71_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_52_, v___x_70_, v___f_69_, v_result_67_, v___x_68_, lean_box(0), lean_box(0));
v___x_72_ = lean_nat_sub(v___x_56_, v___x_68_);
v___x_73_ = lean_string_utf8_get(v_string_51_, v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_box_uint32(v___x_73_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = lean_nat_sub(v___x_56_, v___x_57_);
v___x_77_ = lean_string_utf8_get(v_string_51_, v___x_76_);
lean_dec(v___x_76_);
lean_dec_ref(v_string_51_);
v___x_78_ = lean_box_uint32(v___x_77_);
v___x_79_ = lean_apply_3(v_f_50_, v___x_75_, v___x_78_, v___x_60_);
v___x_80_ = lean_array_push(v___x_71_, v___x_79_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; uint32_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_string_utf8_get(v_string_51_, v___x_54_);
lean_dec_ref(v_string_51_);
v___x_83_ = lean_box_uint32(v___x_82_);
v___x_84_ = lean_apply_3(v_f_50_, v___x_81_, v___x_83_, v___x_81_);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_57_);
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
uint32_t v_ac_98_; uint32_t v_bc_99_; lean_object* v_bPos_100_; uint32_t v___y_102_; uint32_t v___y_103_; uint32_t v___y_109_; uint8_t v___y_110_; uint32_t v___y_114_; uint8_t v___y_120_; uint32_t v___x_123_; uint8_t v___x_124_; 
v_ac_98_ = lean_string_utf8_get_fast(v_a_92_, v_aPos_94_);
v_bc_99_ = lean_string_utf8_get_fast(v_b_93_, v_bPos_95_);
v_bPos_100_ = lean_string_utf8_next_fast(v_b_93_, v_bPos_95_);
lean_dec(v_bPos_95_);
v___x_123_ = 65;
v___x_124_ = lean_uint32_dec_le(v___x_123_, v_ac_98_);
if (v___x_124_ == 0)
{
v___y_120_ = v___x_124_;
goto v___jp_119_;
}
else
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 90;
v___x_126_ = lean_uint32_dec_le(v_ac_98_, v___x_125_);
v___y_120_ = v___x_126_;
goto v___jp_119_;
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
if (v___y_110_ == 0)
{
v___y_102_ = v___y_109_;
v___y_103_ = v_bc_99_;
goto v___jp_101_;
}
else
{
uint32_t v___x_111_; uint32_t v___x_112_; 
v___x_111_ = 32;
v___x_112_ = lean_uint32_add(v_bc_99_, v___x_111_);
v___y_102_ = v___y_109_;
v___y_103_ = v___x_112_;
goto v___jp_101_;
}
}
v___jp_113_:
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 65;
v___x_116_ = lean_uint32_dec_le(v___x_115_, v_bc_99_);
if (v___x_116_ == 0)
{
v___y_109_ = v___y_114_;
v___y_110_ = v___x_116_;
goto v___jp_108_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 90;
v___x_118_ = lean_uint32_dec_le(v_bc_99_, v___x_117_);
v___y_109_ = v___y_114_;
v___y_110_ = v___x_118_;
goto v___jp_108_;
}
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
v___y_114_ = v_ac_98_;
goto v___jp_113_;
}
else
{
uint32_t v___x_121_; uint32_t v___x_122_; 
v___x_121_ = 32;
v___x_122_ = lean_uint32_add(v_ac_98_, v___x_121_);
v___y_114_ = v___x_122_;
goto v___jp_113_;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go___boxed(lean_object* v_a_127_, lean_object* v_b_128_, lean_object* v_aPos_129_, lean_object* v_bPos_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_127_, v_b_128_, v_aPos_129_, v_bPos_130_);
lean_dec_ref(v_b_128_);
lean_dec_ref(v_a_127_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_133_, v_b_134_, v___x_135_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower___boxed(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(v_a_137_, v_b_138_);
lean_dec_ref(v_b_138_);
lean_dec_ref(v_a_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx(uint8_t v_x_141_){
_start:
{
switch(v_x_141_)
{
case 0:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(0u);
return v___x_142_;
}
case 1:
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(1u);
return v___x_143_;
}
default: 
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(2u);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___boxed(lean_object* v_x_145_){
_start:
{
uint8_t v_x_boxed_146_; lean_object* v_res_147_; 
v_x_boxed_146_ = lean_unbox(v_x_145_);
v_res_147_ = l_Lean_FuzzyMatching_CharType_ctorIdx(v_x_boxed_146_);
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
uint8_t v___y_204_; uint8_t v___y_220_; uint32_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 65;
v___x_226_ = lean_uint32_dec_le(v___x_225_, v_c_202_);
if (v___x_226_ == 0)
{
v___y_220_ = v___x_226_;
goto v___jp_219_;
}
else
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 90;
v___x_228_ = lean_uint32_dec_le(v_c_202_, v___x_227_);
v___y_220_ = v___x_228_;
goto v___jp_219_;
}
v___jp_203_:
{
if (v___y_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = 0;
return v___x_205_;
}
else
{
uint8_t v___x_206_; 
v___x_206_ = 1;
return v___x_206_;
}
}
v___jp_207_:
{
uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = 65;
v___x_209_ = lean_uint32_dec_le(v___x_208_, v_c_202_);
if (v___x_209_ == 0)
{
v___y_204_ = v___x_209_;
goto v___jp_203_;
}
else
{
uint32_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 90;
v___x_211_ = lean_uint32_dec_le(v_c_202_, v___x_210_);
v___y_204_ = v___x_211_;
goto v___jp_203_;
}
}
v___jp_212_:
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 48;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v_c_202_);
if (v___x_214_ == 0)
{
uint8_t v___x_215_; 
v___x_215_ = 2;
return v___x_215_;
}
else
{
uint32_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = 57;
v___x_217_ = lean_uint32_dec_le(v_c_202_, v___x_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 2;
return v___x_218_;
}
else
{
goto v___jp_207_;
}
}
}
v___jp_219_:
{
if (v___y_220_ == 0)
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 97;
v___x_222_ = lean_uint32_dec_le(v___x_221_, v_c_202_);
if (v___x_222_ == 0)
{
goto v___jp_212_;
}
else
{
uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 122;
v___x_224_ = lean_uint32_dec_le(v_c_202_, v___x_223_);
if (v___x_224_ == 0)
{
goto v___jp_212_;
}
else
{
goto v___jp_207_;
}
}
}
else
{
goto v___jp_207_;
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
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(lean_object* v_k_240_){
_start:
{
lean_inc(v_k_240_);
return v_k_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(lean_object* v_k_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(v_k_241_);
lean_dec(v_k_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, uint8_t v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
lean_inc(v_k_247_);
return v_k_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object* v_motive_248_, lean_object* v_ctorIdx_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_k_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_FuzzyMatching_CharRole_ctorElim(v_motive_248_, v_ctorIdx_249_, v_t_boxed_253_, v_h_251_, v_k_252_);
lean_dec(v_k_252_);
lean_dec(v_ctorIdx_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object* v_head_255_){
_start:
{
lean_inc(v_head_255_);
return v_head_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object* v_head_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(v_head_256_);
lean_dec(v_head_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_head_261_){
_start:
{
lean_inc(v_head_261_);
return v_head_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_head_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_FuzzyMatching_CharRole_head_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_head_265_);
lean_dec(v_head_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object* v_tail_268_){
_start:
{
lean_inc(v_tail_268_);
return v_tail_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object* v_tail_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(v_tail_269_);
lean_dec(v_tail_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_tail_274_){
_start:
{
lean_inc(v_tail_274_);
return v_tail_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_tail_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Lean_FuzzyMatching_CharRole_tail_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_tail_278_);
lean_dec(v_tail_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object* v_separator_281_){
_start:
{
lean_inc(v_separator_281_);
return v_separator_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object* v_separator_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(v_separator_282_);
lean_dec(v_separator_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object* v_motive_284_, uint8_t v_t_285_, lean_object* v_h_286_, lean_object* v_separator_287_){
_start:
{
lean_inc(v_separator_287_);
return v_separator_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object* v_motive_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_separator_291_){
_start:
{
uint8_t v_t_boxed_292_; lean_object* v_res_293_; 
v_t_boxed_292_ = lean_unbox(v_t_289_);
v_res_293_ = l_Lean_FuzzyMatching_CharRole_separator_elim(v_motive_288_, v_t_boxed_292_, v_h_290_, v_separator_291_);
lean_dec(v_separator_291_);
return v_res_293_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default(void){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole(void){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object* v_prev_x3f_296_, uint8_t v_curr_297_, lean_object* v_next_x3f_298_){
_start:
{
if (v_curr_297_ == 2)
{
uint8_t v___x_299_; 
v___x_299_ = 2;
return v___x_299_;
}
else
{
if (lean_obj_tag(v_prev_x3f_296_) == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
else
{
lean_object* v_val_301_; uint8_t v___x_302_; 
v_val_301_ = lean_ctor_get(v_prev_x3f_296_, 0);
v___x_302_ = lean_unbox(v_val_301_);
if (v___x_302_ == 2)
{
uint8_t v___x_303_; 
v___x_303_ = 0;
return v___x_303_;
}
else
{
if (v_curr_297_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = lean_unbox(v_val_301_);
if (v___x_305_ == 1)
{
if (lean_obj_tag(v_next_x3f_298_) == 1)
{
lean_object* v_val_306_; uint8_t v___x_307_; 
v_val_306_ = lean_ctor_get(v_next_x3f_298_, 0);
v___x_307_ = lean_unbox(v_val_306_);
if (v___x_307_ == 0)
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = 1;
return v___x_309_;
}
}
else
{
uint8_t v___x_310_; 
v___x_310_ = 1;
return v___x_310_;
}
}
else
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object* v_prev_x3f_312_, lean_object* v_curr_313_, lean_object* v_next_x3f_314_){
_start:
{
uint8_t v_curr_boxed_315_; uint8_t v_res_316_; lean_object* v_r_317_; 
v_curr_boxed_315_ = lean_unbox(v_curr_313_);
v_res_316_ = l_Lean_FuzzyMatching_charRole(v_prev_x3f_312_, v_curr_boxed_315_, v_next_x3f_314_);
lean_dec(v_next_x3f_314_);
lean_dec(v_prev_x3f_312_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_string_318_, lean_object* v_range_319_, lean_object* v_b_320_, lean_object* v_i_321_){
_start:
{
lean_object* v_stop_322_; lean_object* v_step_323_; uint8_t v___y_325_; uint8_t v___x_330_; 
v_stop_322_ = lean_ctor_get(v_range_319_, 1);
v_step_323_ = lean_ctor_get(v_range_319_, 2);
v___x_330_ = lean_nat_dec_lt(v_i_321_, v_stop_322_);
if (v___x_330_ == 0)
{
lean_dec(v_i_321_);
return v_b_320_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_sub(v_i_321_, v___x_331_);
v___x_333_ = lean_string_utf8_get(v_string_318_, v___x_332_);
lean_dec(v___x_332_);
v___x_334_ = l_Lean_FuzzyMatching_charType(v___x_333_);
if (v___x_334_ == 2)
{
uint8_t v___x_335_; 
v___x_335_ = 2;
v___y_325_ = v___x_335_;
goto v___jp_324_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; uint32_t v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(2u);
v___x_337_ = lean_nat_sub(v_i_321_, v___x_336_);
v___x_338_ = lean_string_utf8_get(v_string_318_, v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = l_Lean_FuzzyMatching_charType(v___x_338_);
if (v___x_339_ == 2)
{
uint8_t v___x_340_; 
v___x_340_ = 0;
v___y_325_ = v___x_340_;
goto v___jp_324_;
}
else
{
if (v___x_334_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = 1;
v___y_325_ = v___x_341_;
goto v___jp_324_;
}
else
{
if (v___x_339_ == 1)
{
uint32_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_string_utf8_get(v_string_318_, v_i_321_);
v___x_343_ = l_Lean_FuzzyMatching_charType(v___x_342_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
v___x_344_ = 0;
v___y_325_ = v___x_344_;
goto v___jp_324_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 1;
v___y_325_ = v___x_345_;
goto v___jp_324_;
}
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
v___y_325_ = v___x_346_;
goto v___jp_324_;
}
}
}
}
}
v___jp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_box(v___y_325_);
v___x_327_ = lean_array_push(v_b_320_, v___x_326_);
v___x_328_ = lean_nat_add(v_i_321_, v_step_323_);
lean_dec(v_i_321_);
v_b_320_ = v___x_327_;
v_i_321_ = v___x_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_string_347_, lean_object* v_range_348_, lean_object* v_b_349_, lean_object* v_i_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_347_, v_range_348_, v_b_349_, v_i_350_);
lean_dec_ref(v_range_348_);
lean_dec_ref(v_string_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object* v_string_352_, lean_object* v_range_353_, lean_object* v_b_354_, lean_object* v_i_355_){
_start:
{
lean_object* v_stop_356_; lean_object* v_step_357_; uint8_t v___y_359_; uint8_t v___x_364_; 
v_stop_356_ = lean_ctor_get(v_range_353_, 1);
v_step_357_ = lean_ctor_get(v_range_353_, 2);
v___x_364_ = lean_nat_dec_lt(v_i_355_, v_stop_356_);
if (v___x_364_ == 0)
{
return v_b_354_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_sub(v_i_355_, v___x_365_);
v___x_367_ = lean_string_utf8_get(v_string_352_, v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = l_Lean_FuzzyMatching_charType(v___x_367_);
if (v___x_368_ == 2)
{
uint8_t v___x_369_; 
v___x_369_ = 2;
v___y_359_ = v___x_369_;
goto v___jp_358_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_370_ = lean_unsigned_to_nat(2u);
v___x_371_ = lean_nat_sub(v_i_355_, v___x_370_);
v___x_372_ = lean_string_utf8_get(v_string_352_, v___x_371_);
lean_dec(v___x_371_);
v___x_373_ = l_Lean_FuzzyMatching_charType(v___x_372_);
if (v___x_373_ == 2)
{
uint8_t v___x_374_; 
v___x_374_ = 0;
v___y_359_ = v___x_374_;
goto v___jp_358_;
}
else
{
if (v___x_368_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 1;
v___y_359_ = v___x_375_;
goto v___jp_358_;
}
else
{
if (v___x_373_ == 1)
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_string_utf8_get(v_string_352_, v_i_355_);
v___x_377_ = l_Lean_FuzzyMatching_charType(v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
v___x_378_ = 0;
v___y_359_ = v___x_378_;
goto v___jp_358_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = 1;
v___y_359_ = v___x_379_;
goto v___jp_358_;
}
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 0;
v___y_359_ = v___x_380_;
goto v___jp_358_;
}
}
}
}
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = lean_box(v___y_359_);
v___x_361_ = lean_array_push(v_b_354_, v___x_360_);
v___x_362_ = lean_nat_add(v_i_355_, v_step_357_);
v___x_363_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_352_, v_range_353_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object* v_string_381_, lean_object* v_range_382_, lean_object* v_b_383_, lean_object* v_i_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_381_, v_range_382_, v_b_383_, v_i_384_);
lean_dec(v_i_384_);
lean_dec_ref(v_range_382_);
lean_dec_ref(v_string_381_);
return v_res_385_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object* v_prev_x3f_386_, uint32_t v_curr_387_, lean_object* v_next_x3f_388_){
_start:
{
uint8_t v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_407_; 
if (lean_obj_tag(v_prev_x3f_386_) == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
v___y_407_ = v___x_421_;
goto v___jp_406_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_val_422_ = lean_ctor_get(v_prev_x3f_386_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_prev_x3f_386_);
if (v_isSharedCheck_432_ == 0)
{
v___x_424_ = v_prev_x3f_386_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_dec(v_prev_x3f_386_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint32_t v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_426_ = lean_unbox_uint32(v_val_422_);
lean_dec(v_val_422_);
v___x_427_ = l_Lean_FuzzyMatching_charType(v___x_426_);
v___x_428_ = lean_box(v___x_427_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_428_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v___y_407_ = v___x_430_;
goto v___jp_406_;
}
}
}
v___jp_389_:
{
if (v___y_390_ == 2)
{
uint8_t v___x_393_; 
lean_dec(v___y_392_);
lean_dec(v___y_391_);
v___x_393_ = 2;
return v___x_393_;
}
else
{
if (lean_obj_tag(v___y_391_) == 0)
{
uint8_t v___x_394_; 
lean_dec(v___y_392_);
v___x_394_ = 0;
return v___x_394_;
}
else
{
lean_object* v_val_395_; uint8_t v___x_396_; 
v_val_395_ = lean_ctor_get(v___y_391_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___y_391_, 1);
v___x_396_ = lean_unbox(v_val_395_);
if (v___x_396_ == 2)
{
uint8_t v___x_397_; 
lean_dec(v_val_395_);
lean_dec(v___y_392_);
v___x_397_ = 0;
return v___x_397_;
}
else
{
if (v___y_390_ == 0)
{
uint8_t v___x_398_; 
lean_dec(v_val_395_);
lean_dec(v___y_392_);
v___x_398_ = 1;
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = lean_unbox(v_val_395_);
lean_dec(v_val_395_);
if (v___x_399_ == 1)
{
if (lean_obj_tag(v___y_392_) == 1)
{
lean_object* v_val_400_; uint8_t v___x_401_; 
v_val_400_ = lean_ctor_get(v___y_392_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v___y_392_, 1);
v___x_401_ = lean_unbox(v_val_400_);
lean_dec(v_val_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 1;
return v___x_403_;
}
}
else
{
uint8_t v___x_404_; 
lean_dec(v___y_392_);
v___x_404_ = 1;
return v___x_404_;
}
}
else
{
uint8_t v___x_405_; 
lean_dec(v___y_392_);
v___x_405_ = 0;
return v___x_405_;
}
}
}
}
}
}
v___jp_406_:
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_FuzzyMatching_charType(v_curr_387_);
if (lean_obj_tag(v_next_x3f_388_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
v___y_390_ = v___x_408_;
v___y_391_ = v___y_407_;
v___y_392_ = v___x_409_;
goto v___jp_389_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_420_; 
v_val_410_ = lean_ctor_get(v_next_x3f_388_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_next_x3f_388_);
if (v_isSharedCheck_420_ == 0)
{
v___x_412_ = v_next_x3f_388_;
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v_next_x3f_388_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint32_t v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_414_ = lean_unbox_uint32(v_val_410_);
lean_dec(v_val_410_);
v___x_415_ = l_Lean_FuzzyMatching_charType(v___x_414_);
v___x_416_ = lean_box(v___x_415_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_416_);
v___x_418_ = v___x_412_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
v___y_390_ = v___x_408_;
v___y_391_ = v___y_407_;
v___y_392_ = v___x_418_;
goto v___jp_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* v_prev_x3f_433_, lean_object* v_curr_434_, lean_object* v_next_x3f_435_){
_start:
{
uint32_t v_curr_boxed_436_; uint8_t v_res_437_; lean_object* v_r_438_; 
v_curr_boxed_436_ = lean_unbox_uint32(v_curr_434_);
lean_dec(v_curr_434_);
v_res_437_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_433_, v_curr_boxed_436_, v_next_x3f_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* v_string_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_string_utf8_byte_size(v_string_441_);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_nat_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_string_length(v_string_441_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v_result_448_; lean_object* v___x_449_; uint32_t v___x_450_; uint32_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v_result_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint32_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint32_t v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_result_448_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_string_utf8_get(v_string_441_, v___x_443_);
v___x_451_ = lean_string_utf8_get(v_string_441_, v___x_446_);
v___x_452_ = lean_box_uint32(v___x_451_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
v___x_454_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_449_, v___x_450_, v___x_453_);
v___x_455_ = lean_box(v___x_454_);
v_result_456_ = lean_array_push(v_result_448_, v___x_455_);
v___x_457_ = lean_unsigned_to_nat(2u);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_445_);
lean_ctor_set(v___x_458_, 2, v___x_446_);
v___x_459_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_441_, v___x_458_, v_result_456_, v___x_457_);
lean_dec_ref_known(v___x_458_, 3);
v___x_460_ = lean_nat_sub(v___x_445_, v___x_457_);
v___x_461_ = lean_string_utf8_get(v_string_441_, v___x_460_);
lean_dec(v___x_460_);
v___x_462_ = lean_box_uint32(v___x_461_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
v___x_464_ = lean_nat_sub(v___x_445_, v___x_446_);
v___x_465_ = lean_string_utf8_get(v_string_441_, v___x_464_);
lean_dec(v___x_464_);
v___x_466_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_463_, v___x_465_, v___x_449_);
v___x_467_ = lean_box(v___x_466_);
v___x_468_ = lean_array_push(v___x_459_, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; uint32_t v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_469_ = lean_box(0);
v___x_470_ = lean_string_utf8_get(v_string_441_, v___x_443_);
v___x_471_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_469_, v___x_470_, v___x_469_);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_446_);
v___x_473_ = lean_box(v___x_471_);
v___x_474_ = lean_array_push(v___x_472_, v___x_473_);
return v___x_474_;
}
}
else
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0));
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* v_string_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_476_);
lean_dec_ref(v_string_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* v_s_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* v_s_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_480_);
lean_dec_ref(v_s_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* v_string_482_, lean_object* v_range_483_, lean_object* v_b_484_, lean_object* v_i_485_, lean_object* v_hs_486_, lean_object* v_hl_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_482_, v_range_483_, v_b_484_, v_i_485_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* v_string_489_, lean_object* v_range_490_, lean_object* v_b_491_, lean_object* v_i_492_, lean_object* v_hs_493_, lean_object* v_hl_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_489_, v_range_490_, v_b_491_, v_i_492_, v_hs_493_, v_hl_494_);
lean_dec(v_i_492_);
lean_dec_ref(v_range_490_);
lean_dec_ref(v_string_489_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* v_string_496_, lean_object* v_range_497_, lean_object* v_b_498_, lean_object* v_i_499_, lean_object* v_hs_500_, lean_object* v_hl_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_496_, v_range_497_, v_b_498_, v_i_499_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_string_503_, lean_object* v_range_504_, lean_object* v_b_505_, lean_object* v_i_506_, lean_object* v_hs_507_, lean_object* v_hl_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_503_, v_range_504_, v_b_505_, v_i_506_, v_hs_507_, v_hl_508_);
lean_dec_ref(v_range_504_);
lean_dec_ref(v_string_503_);
return v_res_509_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0(void){
_start:
{
lean_object* v___x_510_; uint16_t v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_int16_of_nat(v___x_510_);
return v___x_511_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default(void){
_start:
{
uint16_t v___x_512_; 
v___x_512_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_512_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore(void){
_start:
{
uint16_t v___x_513_; 
v___x_513_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
return v___x_513_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0(void){
_start:
{
lean_object* v___x_514_; uint16_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(32768u);
v___x_515_ = lean_int16_of_nat(v___x_514_);
return v___x_515_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1(void){
_start:
{
uint16_t v___x_516_; uint16_t v___x_517_; 
v___x_516_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0);
v___x_517_ = lean_int16_neg(v___x_516_);
return v___x_517_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful(void){
_start:
{
uint16_t v___x_518_; 
v___x_518_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
return v___x_518_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t v_x_519_){
_start:
{
uint16_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_521_ = lean_int16_dec_le(v_x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* v_x_522_){
_start:
{
uint16_t v_x_boxed_523_; uint8_t v_res_524_; lean_object* v_r_525_; 
v_x_boxed_523_ = lean_unbox(v_x_522_);
v_res_524_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t v_x_526_, lean_object* v_f_527_){
_start:
{
uint16_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_529_ = lean_int16_dec_le(v_x_526_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; uint16_t v___x_532_; 
v___x_530_ = lean_box(v_x_526_);
v___x_531_ = lean_apply_1(v_f_527_, v___x_530_);
v___x_532_ = lean_unbox(v___x_531_);
return v___x_532_;
}
else
{
lean_dec_ref(v_f_527_);
return v_x_526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* v_x_533_, lean_object* v_f_534_){
_start:
{
uint16_t v_x_boxed_535_; uint16_t v_res_536_; lean_object* v_r_537_; 
v_x_boxed_535_ = lean_unbox(v_x_533_);
v_res_536_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_boxed_535_, v_f_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t v_x_538_){
_start:
{
uint16_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_540_ = lean_int16_dec_le(v_x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(v_x_538_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* v_x_544_){
_start:
{
uint16_t v_x_boxed_545_; lean_object* v_res_546_; 
v_x_boxed_545_ = lean_unbox(v_x_544_);
v_res_546_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_boxed_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t v_x_547_){
_start:
{
uint16_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_549_ = lean_int16_dec_le(v_x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_int16_to_int(v_x_547_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; 
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* v_x_553_){
_start:
{
uint16_t v_x_boxed_554_; lean_object* v_res_555_; 
v_x_boxed_554_ = lean_unbox(v_x_553_);
v_res_555_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_554_);
return v_res_555_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
v___x_560_ = lean_unsigned_to_nat(2u);
v___x_561_ = lean_unsigned_to_nat(127u);
v___x_562_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
v___x_563_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
v___x_564_ = l_mkPanicMessageWithDecl(v___x_563_, v___x_562_, v___x_561_, v___x_560_, v___x_559_);
return v___x_564_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t v_x_565_){
_start:
{
uint16_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_567_ = lean_int16_dec_eq(v_x_565_, v___x_566_);
if (v___x_567_ == 0)
{
return v_x_565_;
}
else
{
uint16_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint16_t v___x_572_; 
v___x_568_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_569_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_570_ = lean_box(v___x_568_);
v___x_571_ = l_panic___redArg(v___x_570_, v___x_569_);
lean_dec(v___x_570_);
v___x_572_ = lean_unbox(v___x_571_);
lean_dec(v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* v_x_573_){
_start:
{
uint16_t v_x_boxed_574_; uint16_t v_res_575_; lean_object* v_r_576_; 
v_x_boxed_574_ = lean_unbox(v_x_573_);
v_res_575_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_boxed_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t v_missScore_577_, uint16_t v_matchScore_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_int16_dec_le(v_missScore_577_, v_matchScore_578_);
if (v___x_579_ == 0)
{
return v_missScore_577_;
}
else
{
return v_matchScore_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* v_missScore_580_, lean_object* v_matchScore_581_){
_start:
{
uint16_t v_missScore_boxed_582_; uint16_t v_matchScore_boxed_583_; uint16_t v_res_584_; lean_object* v_r_585_; 
v_missScore_boxed_582_ = lean_unbox(v_missScore_580_);
v_matchScore_boxed_583_ = lean_unbox(v_matchScore_581_);
v_res_584_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_boxed_582_, v_matchScore_boxed_583_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* v_word_586_, lean_object* v_patternIdx_587_, lean_object* v_wordIdx_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = lean_string_length(v_word_586_);
v___x_590_ = lean_nat_mul(v_patternIdx_587_, v___x_589_);
v___x_591_ = lean_unsigned_to_nat(2u);
v___x_592_ = lean_nat_mul(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_nat_mul(v_wordIdx_588_, v___x_591_);
v___x_594_ = lean_nat_add(v___x_592_, v___x_593_);
lean_dec(v___x_593_);
lean_dec(v___x_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* v_word_595_, lean_object* v_patternIdx_596_, lean_object* v_wordIdx_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(v_word_595_, v_patternIdx_596_, v_wordIdx_597_);
lean_dec(v_wordIdx_597_);
lean_dec(v_patternIdx_596_);
lean_dec_ref(v_word_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* v_word_599_, lean_object* v_patternIdx_600_, lean_object* v_wordIdx_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_string_length(v_word_599_);
v___x_603_ = lean_nat_mul(v_patternIdx_600_, v___x_602_);
v___x_604_ = lean_nat_add(v___x_603_, v_wordIdx_601_);
lean_dec(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* v_word_605_, lean_object* v_patternIdx_606_, lean_object* v_wordIdx_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(v_word_605_, v_patternIdx_606_, v_wordIdx_607_);
lean_dec(v_wordIdx_607_);
lean_dec(v_patternIdx_606_);
lean_dec_ref(v_word_605_);
return v_res_608_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* v_word_609_, lean_object* v_result_610_, lean_object* v_patternIdx_611_, lean_object* v_wordIdx_612_){
_start:
{
uint16_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint16_t v___x_622_; 
v___x_613_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_614_ = lean_string_length(v_word_609_);
v___x_615_ = lean_nat_mul(v_patternIdx_611_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(2u);
v___x_617_ = lean_nat_mul(v___x_615_, v___x_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_nat_mul(v_wordIdx_612_, v___x_616_);
v___x_619_ = lean_nat_add(v___x_617_, v___x_618_);
lean_dec(v___x_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(v___x_613_);
v___x_621_ = lean_array_get(v___x_620_, v_result_610_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v___x_620_);
v___x_622_ = lean_unbox(v___x_621_);
lean_dec(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* v_word_623_, lean_object* v_result_624_, lean_object* v_patternIdx_625_, lean_object* v_wordIdx_626_){
_start:
{
uint16_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_623_, v_result_624_, v_patternIdx_625_, v_wordIdx_626_);
lean_dec(v_wordIdx_626_);
lean_dec(v_patternIdx_625_);
lean_dec_ref(v_result_624_);
lean_dec_ref(v_word_623_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* v_word_629_, lean_object* v_result_630_, lean_object* v_patternIdx_631_, lean_object* v_wordIdx_632_){
_start:
{
uint16_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint16_t v___x_644_; 
v___x_633_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_634_ = lean_string_length(v_word_629_);
v___x_635_ = lean_nat_mul(v_patternIdx_631_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(2u);
v___x_637_ = lean_nat_mul(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_nat_mul(v_wordIdx_632_, v___x_636_);
v___x_639_ = lean_nat_add(v___x_637_, v___x_638_);
lean_dec(v___x_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v___x_639_, v___x_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(v___x_633_);
v___x_643_ = lean_array_get(v___x_642_, v_result_630_, v___x_641_);
lean_dec(v___x_641_);
lean_dec(v___x_642_);
v___x_644_ = lean_unbox(v___x_643_);
lean_dec(v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* v_word_645_, lean_object* v_result_646_, lean_object* v_patternIdx_647_, lean_object* v_wordIdx_648_){
_start:
{
uint16_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_645_, v_result_646_, v_patternIdx_647_, v_wordIdx_648_);
lean_dec(v_wordIdx_648_);
lean_dec(v_patternIdx_647_);
lean_dec_ref(v_result_646_);
lean_dec_ref(v_word_645_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* v_word_651_, lean_object* v_result_652_, lean_object* v_patternIdx_653_, lean_object* v_wordIdx_654_, uint16_t v_missValue_655_, uint16_t v_matchValue_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_idx_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_657_ = lean_string_length(v_word_651_);
v___x_658_ = lean_nat_mul(v_patternIdx_653_, v___x_657_);
v___x_659_ = lean_unsigned_to_nat(2u);
v___x_660_ = lean_nat_mul(v___x_658_, v___x_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_nat_mul(v_wordIdx_654_, v___x_659_);
v_idx_662_ = lean_nat_add(v___x_660_, v___x_661_);
lean_dec(v___x_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(v_missValue_655_);
v___x_664_ = lean_array_set(v_result_652_, v_idx_662_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_idx_662_, v___x_665_);
lean_dec(v_idx_662_);
v___x_667_ = lean_box(v_matchValue_656_);
v___x_668_ = lean_array_set(v___x_664_, v___x_666_, v___x_667_);
lean_dec(v___x_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* v_word_669_, lean_object* v_result_670_, lean_object* v_patternIdx_671_, lean_object* v_wordIdx_672_, lean_object* v_missValue_673_, lean_object* v_matchValue_674_){
_start:
{
uint16_t v_missValue_boxed_675_; uint16_t v_matchValue_boxed_676_; lean_object* v_res_677_; 
v_missValue_boxed_675_ = lean_unbox(v_missValue_673_);
v_matchValue_boxed_676_ = lean_unbox(v_matchValue_674_);
v_res_677_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_669_, v_result_670_, v_patternIdx_671_, v_wordIdx_672_, v_missValue_boxed_675_, v_matchValue_boxed_676_);
lean_dec(v_wordIdx_672_);
lean_dec(v_patternIdx_671_);
lean_dec_ref(v_word_669_);
return v_res_677_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0(void){
_start:
{
lean_object* v___x_678_; uint16_t v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_int16_of_nat(v___x_678_);
return v___x_679_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1(void){
_start:
{
lean_object* v___x_680_; uint16_t v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(3u);
v___x_681_ = lean_int16_of_nat(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t v_wordRole_682_, uint8_t v_wordStart_683_){
_start:
{
if (v_wordStart_683_ == 0)
{
if (v_wordRole_682_ == 0)
{
uint16_t v___x_684_; 
v___x_684_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
return v___x_684_;
}
else
{
uint16_t v___x_685_; 
v___x_685_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_685_;
}
}
else
{
uint16_t v___x_686_; 
v___x_686_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* v_wordRole_687_, lean_object* v_wordStart_688_){
_start:
{
uint8_t v_wordRole_boxed_689_; uint8_t v_wordStart_boxed_690_; uint16_t v_res_691_; lean_object* v_r_692_; 
v_wordRole_boxed_689_ = lean_unbox(v_wordRole_687_);
v_wordStart_boxed_690_ = lean_unbox(v_wordStart_688_);
v_res_691_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_boxed_689_, v_wordStart_boxed_690_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t v_patternChar_693_, uint32_t v_wordChar_694_, uint8_t v_patternRole_695_, uint8_t v_wordRole_696_){
_start:
{
uint32_t v___y_698_; uint32_t v___y_699_; uint32_t v___y_703_; uint8_t v___y_704_; uint32_t v___y_708_; uint8_t v___y_714_; uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 65;
v___x_718_ = lean_uint32_dec_le(v___x_717_, v_patternChar_693_);
if (v___x_718_ == 0)
{
v___y_714_ = v___x_718_;
goto v___jp_713_;
}
else
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 90;
v___x_720_ = lean_uint32_dec_le(v_patternChar_693_, v___x_719_);
v___y_714_ = v___x_720_;
goto v___jp_713_;
}
v___jp_697_:
{
uint8_t v___x_700_; 
v___x_700_ = lean_uint32_dec_eq(v___y_698_, v___y_699_);
if (v___x_700_ == 0)
{
return v___x_700_;
}
else
{
if (v_patternRole_695_ == 0)
{
if (v_wordRole_696_ == 0)
{
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
else
{
return v___x_700_;
}
}
}
v___jp_702_:
{
if (v___y_704_ == 0)
{
v___y_698_ = v___y_703_;
v___y_699_ = v_wordChar_694_;
goto v___jp_697_;
}
else
{
uint32_t v___x_705_; uint32_t v___x_706_; 
v___x_705_ = 32;
v___x_706_ = lean_uint32_add(v_wordChar_694_, v___x_705_);
v___y_698_ = v___y_703_;
v___y_699_ = v___x_706_;
goto v___jp_697_;
}
}
v___jp_707_:
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 65;
v___x_710_ = lean_uint32_dec_le(v___x_709_, v_wordChar_694_);
if (v___x_710_ == 0)
{
v___y_703_ = v___y_708_;
v___y_704_ = v___x_710_;
goto v___jp_702_;
}
else
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 90;
v___x_712_ = lean_uint32_dec_le(v_wordChar_694_, v___x_711_);
v___y_703_ = v___y_708_;
v___y_704_ = v___x_712_;
goto v___jp_702_;
}
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
v___y_708_ = v_patternChar_693_;
goto v___jp_707_;
}
else
{
uint32_t v___x_715_; uint32_t v___x_716_; 
v___x_715_ = 32;
v___x_716_ = lean_uint32_add(v_patternChar_693_, v___x_715_);
v___y_708_ = v___x_716_;
goto v___jp_707_;
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
uint16_t v_score_743_; uint16_t v_score_748_; lean_object* v___x_753_; uint16_t v_score_755_; uint16_t v_score_764_; uint32_t v___x_767_; uint32_t v___x_768_; uint8_t v___x_769_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v_score_764_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_767_ = lean_string_utf8_get(v_pattern_735_, v_patternIdx_737_);
v___x_768_ = lean_string_utf8_get(v_word_736_, v_wordIdx_738_);
v___x_769_ = lean_uint32_dec_eq(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
if (v_patternRole_739_ == 0)
{
if (v_wordRole_740_ == 0)
{
goto v___jp_765_;
}
else
{
v_score_755_ = v_score_764_;
goto v___jp_754_;
}
}
else
{
v_score_755_ = v_score_764_;
goto v___jp_754_;
}
}
else
{
goto v___jp_765_;
}
v___jp_742_:
{
uint16_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_745_ = lean_int16_dec_le(v_consecutive_741_, v___x_744_);
if (v___x_745_ == 0)
{
uint16_t v_score_746_; 
v_score_746_ = lean_int16_add(v_score_743_, v_consecutive_741_);
return v_score_746_;
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
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_string_length(v_word_736_);
v___x_757_ = lean_nat_sub(v___x_756_, v___x_753_);
v___x_758_ = lean_nat_dec_eq(v_wordIdx_738_, v___x_757_);
lean_dec(v___x_757_);
if (v___x_758_ == 0)
{
v_score_748_ = v_score_755_;
goto v___jp_747_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_string_length(v_pattern_735_);
v___x_760_ = lean_nat_sub(v___x_759_, v___x_753_);
v___x_761_ = lean_nat_dec_eq(v_patternIdx_737_, v___x_760_);
lean_dec(v___x_760_);
if (v___x_761_ == 0)
{
v_score_748_ = v_score_755_;
goto v___jp_747_;
}
else
{
uint16_t v___x_762_; uint16_t v_score_763_; 
v___x_762_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
v_score_763_ = lean_int16_add(v_score_755_, v___x_762_);
v_score_748_ = v_score_763_;
goto v___jp_747_;
}
}
}
v___jp_765_:
{
uint16_t v_score_766_; 
v_score_766_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
v_score_755_ = v_score_766_;
goto v___jp_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* v_pattern_770_, lean_object* v_word_771_, lean_object* v_patternIdx_772_, lean_object* v_wordIdx_773_, lean_object* v_patternRole_774_, lean_object* v_wordRole_775_, lean_object* v_consecutive_776_){
_start:
{
uint8_t v_patternRole_boxed_777_; uint8_t v_wordRole_boxed_778_; uint16_t v_consecutive_boxed_779_; uint16_t v_res_780_; lean_object* v_r_781_; 
v_patternRole_boxed_777_ = lean_unbox(v_patternRole_774_);
v_wordRole_boxed_778_ = lean_unbox(v_wordRole_775_);
v_consecutive_boxed_779_ = lean_unbox(v_consecutive_776_);
v_res_780_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_770_, v_word_771_, v_patternIdx_772_, v_wordIdx_773_, v_patternRole_boxed_777_, v_wordRole_boxed_778_, v_consecutive_boxed_779_);
lean_dec(v_wordIdx_773_);
lean_dec(v_patternIdx_772_);
lean_dec_ref(v_word_771_);
lean_dec_ref(v_pattern_770_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* v_msg_782_){
_start:
{
uint16_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint16_t v___x_786_; 
v___x_783_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_784_ = lean_box(v___x_783_);
v___x_785_ = lean_panic_fn_borrowed(v___x_784_, v_msg_782_);
lean_dec(v___x_784_);
v___x_786_ = lean_unbox(v___x_785_);
lean_dec(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* v_msg_787_){
_start:
{
uint16_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* v___x_790_, lean_object* v_a_791_, uint16_t v_x_792_){
_start:
{
uint16_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_794_ = lean_int16_dec_le(v_x_792_, v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_le(v___x_790_, v_a_791_);
if (v___x_795_ == 0)
{
return v_x_792_;
}
else
{
uint16_t v___x_796_; uint16_t v___x_797_; 
v___x_796_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_797_ = lean_int16_add(v_x_792_, v___x_796_);
return v___x_797_;
}
}
else
{
return v_x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
uint16_t v_x_boxed_801_; uint16_t v_res_802_; lean_object* v_r_803_; 
v_x_boxed_801_ = lean_unbox(v_x_800_);
v_res_802_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_798_, v_a_799_, v_x_boxed_801_);
lean_dec(v_a_799_);
lean_dec(v___x_798_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* v_pattern_804_, lean_object* v_word_805_, lean_object* v_a_806_, lean_object* v_a_807_, uint8_t v___x_808_, uint8_t v___x_809_, lean_object* v___x_810_, uint16_t v_x_811_){
_start:
{
uint16_t v_matchScore_812_; uint8_t v___x_813_; 
v_matchScore_812_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_813_ = lean_int16_dec_le(v_x_811_, v_matchScore_812_);
if (v___x_813_ == 0)
{
uint16_t v___x_814_; uint16_t v___x_815_; uint16_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint16_t v___x_819_; uint16_t v___x_820_; 
v___x_814_ = l_instInhabitedInt16;
v___x_815_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_804_, v_word_805_, v_a_806_, v_a_807_, v___x_808_, v___x_809_, v_matchScore_812_);
v___x_816_ = lean_int16_add(v_x_811_, v___x_815_);
v___x_817_ = lean_box(v___x_814_);
v___x_818_ = lean_array_get(v___x_817_, v___x_810_, v_a_807_);
lean_dec(v___x_817_);
v___x_819_ = lean_unbox(v___x_818_);
lean_dec(v___x_818_);
v___x_820_ = lean_int16_sub(v___x_816_, v___x_819_);
return v___x_820_;
}
else
{
return v_x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* v_pattern_821_, lean_object* v_word_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v___x_827_, lean_object* v_x_828_){
_start:
{
uint8_t v___x_3248__boxed_829_; uint8_t v___x_3249__boxed_830_; uint16_t v_x_boxed_831_; uint16_t v_res_832_; lean_object* v_r_833_; 
v___x_3248__boxed_829_ = lean_unbox(v___x_825_);
v___x_3249__boxed_830_ = lean_unbox(v___x_826_);
v_x_boxed_831_ = lean_unbox(v_x_828_);
v_res_832_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_821_, v_word_822_, v_a_823_, v_a_824_, v___x_3248__boxed_829_, v___x_3249__boxed_830_, v___x_827_, v_x_boxed_831_);
lean_dec_ref(v___x_827_);
lean_dec(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_word_822_);
lean_dec_ref(v_pattern_821_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* v_pattern_834_, lean_object* v_word_835_, lean_object* v_a_836_, lean_object* v_a_837_, uint8_t v___x_838_, uint8_t v___x_839_, uint16_t v___x_840_, uint16_t v_x_841_){
_start:
{
uint16_t v___y_843_; uint16_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_847_ = lean_int16_dec_le(v_x_841_, v___x_846_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; 
v___x_848_ = lean_int16_dec_eq(v___x_840_, v___x_846_);
if (v___x_848_ == 0)
{
v___y_843_ = v___x_840_;
goto v___jp_842_;
}
else
{
lean_object* v___x_849_; uint16_t v___x_850_; 
v___x_849_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_850_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_849_);
v___y_843_ = v___x_850_;
goto v___jp_842_;
}
}
else
{
return v_x_841_;
}
v___jp_842_:
{
uint16_t v___x_844_; uint16_t v___x_845_; 
v___x_844_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_834_, v_word_835_, v_a_836_, v_a_837_, v___x_838_, v___x_839_, v___y_843_);
v___x_845_ = lean_int16_add(v_x_841_, v___x_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* v_pattern_851_, lean_object* v_word_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_x_858_){
_start:
{
uint8_t v___x_3288__boxed_859_; uint8_t v___x_3289__boxed_860_; uint16_t v___x_3290__boxed_861_; uint16_t v_x_boxed_862_; uint16_t v_res_863_; lean_object* v_r_864_; 
v___x_3288__boxed_859_ = lean_unbox(v___x_855_);
v___x_3289__boxed_860_ = lean_unbox(v___x_856_);
v___x_3290__boxed_861_ = lean_unbox(v___x_857_);
v_x_boxed_862_ = lean_unbox(v_x_858_);
v_res_863_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_851_, v_word_852_, v_a_853_, v_a_854_, v___x_3288__boxed_859_, v___x_3289__boxed_860_, v___x_3290__boxed_861_, v_x_boxed_862_);
lean_dec(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_word_852_);
lean_dec_ref(v_pattern_851_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg(lean_object* v_word_865_, lean_object* v_a_866_, lean_object* v_pattern_867_, lean_object* v_patternRoles_868_, lean_object* v_wordRoles_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_range_872_, lean_object* v_b_873_, lean_object* v_i_874_){
_start:
{
lean_object* v_stop_875_; lean_object* v_step_876_; uint8_t v___x_877_; 
v_stop_875_ = lean_ctor_get(v_range_872_, 1);
v_step_876_ = lean_ctor_get(v_range_872_, 2);
v___x_877_ = lean_nat_dec_lt(v_i_874_, v_stop_875_);
if (v___x_877_ == 0)
{
lean_dec(v_i_874_);
return v_b_873_;
}
else
{
lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_992_; 
v_fst_878_ = lean_ctor_get(v_b_873_, 0);
v_snd_879_ = lean_ctor_get(v_b_873_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_b_873_);
if (v_isSharedCheck_992_ == 0)
{
v___x_881_ = v_b_873_;
v_isShared_882_ = v_isSharedCheck_992_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_snd_879_);
lean_inc(v_fst_878_);
lean_dec(v_b_873_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_992_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; uint16_t v___y_885_; lean_object* v_runLengths_886_; uint16_t v_matchScore_887_; uint16_t v___y_905_; lean_object* v___y_906_; uint16_t v___y_907_; uint8_t v___x_909_; uint16_t v_matchScore_910_; uint8_t v___x_911_; uint16_t v___x_912_; uint16_t v___y_914_; uint8_t v___x_973_; 
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_909_ = 0;
v_matchScore_910_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_911_ = lean_nat_dec_le(v___x_883_, v_a_866_);
v___x_912_ = l_instInhabitedInt16;
v___x_973_ = lean_nat_dec_le(v___x_883_, v_i_874_);
if (v___x_973_ == 0)
{
v___y_914_ = v_matchScore_910_;
goto v___jp_913_;
}
else
{
lean_object* v___x_974_; uint16_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint16_t v___x_987_; uint16_t v___x_988_; uint8_t v___x_989_; 
v___x_974_ = lean_nat_sub(v_i_874_, v___x_883_);
v___x_975_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_976_ = lean_string_length(v_word_865_);
v___x_977_ = lean_nat_mul(v_a_866_, v___x_976_);
v___x_978_ = lean_unsigned_to_nat(2u);
v___x_979_ = lean_nat_mul(v___x_977_, v___x_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_nat_mul(v___x_974_, v___x_978_);
lean_dec(v___x_974_);
v___x_981_ = lean_nat_add(v___x_979_, v___x_980_);
lean_dec(v___x_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(v___x_975_);
v___x_983_ = lean_array_get(v___x_982_, v_fst_878_, v___x_981_);
lean_dec(v___x_982_);
v___x_984_ = lean_nat_add(v___x_981_, v___x_883_);
lean_dec(v___x_981_);
v___x_985_ = lean_box(v___x_975_);
v___x_986_ = lean_array_get(v___x_985_, v_fst_878_, v___x_984_);
lean_dec(v___x_984_);
lean_dec(v___x_985_);
v___x_987_ = lean_unbox(v___x_983_);
v___x_988_ = lean_unbox(v___x_986_);
v___x_989_ = lean_int16_dec_le(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
uint16_t v___x_990_; 
lean_dec(v___x_986_);
v___x_990_ = lean_unbox(v___x_983_);
lean_dec(v___x_983_);
v___y_914_ = v___x_990_;
goto v___jp_913_;
}
else
{
uint16_t v___x_991_; 
lean_dec(v___x_983_);
v___x_991_ = lean_unbox(v___x_986_);
lean_dec(v___x_986_);
v___y_914_ = v___x_991_;
goto v___jp_913_;
}
}
v___jp_884_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_idx_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_888_ = lean_string_length(v_word_865_);
v___x_889_ = lean_nat_mul(v_a_866_, v___x_888_);
v___x_890_ = lean_unsigned_to_nat(2u);
v___x_891_ = lean_nat_mul(v___x_889_, v___x_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_nat_mul(v_i_874_, v___x_890_);
v_idx_893_ = lean_nat_add(v___x_891_, v___x_892_);
lean_dec(v___x_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(v___y_885_);
v___x_895_ = lean_array_set(v_fst_878_, v_idx_893_, v___x_894_);
v___x_896_ = lean_nat_add(v_idx_893_, v___x_883_);
lean_dec(v_idx_893_);
v___x_897_ = lean_box(v_matchScore_887_);
v___x_898_ = lean_array_set(v___x_895_, v___x_896_, v___x_897_);
lean_dec(v___x_896_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_runLengths_886_);
lean_ctor_set(v___x_881_, 0, v___x_898_);
v___x_900_ = v___x_881_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_runLengths_886_);
v___x_900_ = v_reuseFailAlloc_903_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_nat_add(v_i_874_, v_step_876_);
lean_dec(v_i_874_);
v_b_873_ = v___x_900_;
v_i_874_ = v___x_901_;
goto _start;
}
}
v___jp_904_:
{
uint16_t v___x_908_; 
v___x_908_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_871_, v_i_874_, v___y_907_);
v___y_885_ = v___y_905_;
v_runLengths_886_ = v___y_906_;
v_matchScore_887_ = v___x_908_;
goto v___jp_884_;
}
v___jp_913_:
{
uint32_t v___x_915_; uint32_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; uint8_t v___x_923_; 
v___x_915_ = lean_string_utf8_get(v_pattern_867_, v_a_866_);
v___x_916_ = lean_string_utf8_get(v_word_865_, v_i_874_);
v___x_917_ = lean_box(v___x_909_);
v___x_918_ = lean_array_get(v___x_917_, v_patternRoles_868_, v_a_866_);
lean_dec(v___x_917_);
v___x_919_ = lean_box(v___x_909_);
v___x_920_ = lean_array_get(v___x_919_, v_wordRoles_869_, v_i_874_);
lean_dec(v___x_919_);
v___x_921_ = lean_unbox(v___x_918_);
v___x_922_ = lean_unbox(v___x_920_);
v___x_923_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_915_, v___x_916_, v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_dec(v___x_920_);
lean_dec(v___x_918_);
v___y_885_ = v___y_914_;
v_runLengths_886_ = v_snd_879_;
v_matchScore_887_ = v_matchScore_910_;
goto v___jp_884_;
}
else
{
if (v___x_911_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint16_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; uint8_t v___x_931_; uint16_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint16_t v___x_935_; uint16_t v___x_936_; uint8_t v___x_937_; 
v___x_924_ = lean_string_length(v_word_865_);
v___x_925_ = lean_nat_mul(v_a_866_, v___x_924_);
v___x_926_ = lean_nat_add(v___x_925_, v_i_874_);
lean_dec(v___x_925_);
v___x_927_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_928_ = lean_box(v___x_927_);
v___x_929_ = lean_array_set(v_snd_879_, v___x_926_, v___x_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_unbox(v___x_918_);
lean_dec(v___x_918_);
v___x_931_ = lean_unbox(v___x_920_);
lean_dec(v___x_920_);
v___x_932_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_867_, v_word_865_, v_a_866_, v_i_874_, v___x_930_, v___x_931_, v_matchScore_910_);
v___x_933_ = lean_box(v___x_912_);
v___x_934_ = lean_array_get(v___x_933_, v___x_870_, v_i_874_);
lean_dec(v___x_933_);
v___x_935_ = lean_unbox(v___x_934_);
lean_dec(v___x_934_);
v___x_936_ = lean_int16_sub(v___x_932_, v___x_935_);
v___x_937_ = lean_int16_dec_eq(v___x_936_, v_matchScore_910_);
if (v___x_937_ == 0)
{
v___y_885_ = v___y_914_;
v_runLengths_886_ = v___x_929_;
v_matchScore_887_ = v___x_936_;
goto v___jp_884_;
}
else
{
lean_object* v___x_938_; uint16_t v___x_939_; 
v___x_938_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_939_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_938_);
v___y_885_ = v___y_914_;
v_runLengths_886_ = v___x_929_;
v_matchScore_887_ = v___x_939_;
goto v___jp_884_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint16_t v___x_947_; uint16_t v___x_948_; uint16_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint16_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; uint8_t v___x_962_; uint16_t v___x_963_; uint16_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; uint16_t v___x_970_; uint16_t v___x_971_; uint8_t v___x_972_; 
v___x_940_ = lean_nat_sub(v_a_866_, v___x_883_);
v___x_941_ = lean_nat_sub(v_i_874_, v___x_883_);
v___x_942_ = lean_string_length(v_word_865_);
v___x_943_ = lean_nat_mul(v___x_940_, v___x_942_);
lean_dec(v___x_940_);
v___x_944_ = lean_nat_add(v___x_943_, v___x_941_);
v___x_945_ = lean_box(v___x_912_);
v___x_946_ = lean_array_get(v___x_945_, v_snd_879_, v___x_944_);
lean_dec(v___x_944_);
lean_dec(v___x_945_);
v___x_947_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_948_ = lean_unbox(v___x_946_);
lean_dec(v___x_946_);
v___x_949_ = lean_int16_add(v___x_948_, v___x_947_);
v___x_950_ = lean_nat_mul(v_a_866_, v___x_942_);
v___x_951_ = lean_nat_add(v___x_950_, v_i_874_);
lean_dec(v___x_950_);
v___x_952_ = lean_box(v___x_949_);
v___x_953_ = lean_array_set(v_snd_879_, v___x_951_, v___x_952_);
lean_dec(v___x_951_);
v___x_954_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_955_ = lean_unsigned_to_nat(2u);
v___x_956_ = lean_nat_mul(v___x_943_, v___x_955_);
lean_dec(v___x_943_);
v___x_957_ = lean_nat_mul(v___x_941_, v___x_955_);
lean_dec(v___x_941_);
v___x_958_ = lean_nat_add(v___x_956_, v___x_957_);
lean_dec(v___x_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(v___x_954_);
v___x_960_ = lean_array_get(v___x_959_, v_fst_878_, v___x_958_);
lean_dec(v___x_959_);
v___x_961_ = lean_unbox(v___x_918_);
v___x_962_ = lean_unbox(v___x_920_);
v___x_963_ = lean_unbox(v___x_960_);
lean_dec(v___x_960_);
v___x_964_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_867_, v_word_865_, v_a_866_, v_i_874_, v___x_961_, v___x_962_, v___x_870_, v___x_963_);
v___x_965_ = lean_nat_add(v___x_958_, v___x_883_);
lean_dec(v___x_958_);
v___x_966_ = lean_box(v___x_954_);
v___x_967_ = lean_array_get(v___x_966_, v_fst_878_, v___x_965_);
lean_dec(v___x_965_);
lean_dec(v___x_966_);
v___x_968_ = lean_unbox(v___x_918_);
lean_dec(v___x_918_);
v___x_969_ = lean_unbox(v___x_920_);
lean_dec(v___x_920_);
v___x_970_ = lean_unbox(v___x_967_);
lean_dec(v___x_967_);
v___x_971_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_867_, v_word_865_, v_a_866_, v_i_874_, v___x_968_, v___x_969_, v___x_949_, v___x_970_);
v___x_972_ = lean_int16_dec_le(v___x_964_, v___x_971_);
if (v___x_972_ == 0)
{
v___y_905_ = v___y_914_;
v___y_906_ = v___x_953_;
v___y_907_ = v___x_964_;
goto v___jp_904_;
}
else
{
v___y_905_ = v___y_914_;
v___y_906_ = v___x_953_;
v___y_907_ = v___x_971_;
goto v___jp_904_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg___boxed(lean_object* v_word_993_, lean_object* v_a_994_, lean_object* v_pattern_995_, lean_object* v_patternRoles_996_, lean_object* v_wordRoles_997_, lean_object* v___x_998_, lean_object* v___x_999_, lean_object* v_range_1000_, lean_object* v_b_1001_, lean_object* v_i_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg(v_word_993_, v_a_994_, v_pattern_995_, v_patternRoles_996_, v_wordRoles_997_, v___x_998_, v___x_999_, v_range_1000_, v_b_1001_, v_i_1002_);
lean_dec_ref(v_range_1000_);
lean_dec(v___x_999_);
lean_dec_ref(v___x_998_);
lean_dec_ref(v_wordRoles_997_);
lean_dec_ref(v_patternRoles_996_);
lean_dec_ref(v_pattern_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_word_993_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* v___x_1004_, lean_object* v_word_1005_, lean_object* v_a_1006_, lean_object* v_pattern_1007_, lean_object* v_patternRoles_1008_, lean_object* v_wordRoles_1009_, lean_object* v___x_1010_, lean_object* v_range_1011_, lean_object* v_b_1012_, lean_object* v_i_1013_){
_start:
{
lean_object* v_stop_1014_; lean_object* v_step_1015_; uint8_t v___x_1016_; 
v_stop_1014_ = lean_ctor_get(v_range_1011_, 1);
v_step_1015_ = lean_ctor_get(v_range_1011_, 2);
v___x_1016_ = lean_nat_dec_lt(v_i_1013_, v_stop_1014_);
if (v___x_1016_ == 0)
{
return v_b_1012_;
}
else
{
lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1131_; 
v_fst_1017_ = lean_ctor_get(v_b_1012_, 0);
v_snd_1018_ = lean_ctor_get(v_b_1012_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_b_1012_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1020_ = v_b_1012_;
v_isShared_1021_ = v_isSharedCheck_1131_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_inc(v_fst_1017_);
lean_dec(v_b_1012_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1131_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; uint16_t v___y_1024_; lean_object* v_runLengths_1025_; uint16_t v_matchScore_1026_; lean_object* v___y_1044_; uint16_t v___y_1045_; uint16_t v___y_1046_; uint8_t v___x_1048_; uint16_t v_matchScore_1049_; uint16_t v___x_1050_; uint8_t v___x_1051_; uint16_t v___y_1053_; uint8_t v___x_1112_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1048_ = 0;
v_matchScore_1049_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1050_ = l_instInhabitedInt16;
v___x_1051_ = lean_nat_dec_le(v___x_1022_, v_a_1006_);
v___x_1112_ = lean_nat_dec_le(v___x_1022_, v_i_1013_);
if (v___x_1112_ == 0)
{
v___y_1053_ = v_matchScore_1049_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1113_; uint16_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint16_t v___x_1126_; uint16_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1113_ = lean_nat_sub(v_i_1013_, v___x_1022_);
v___x_1114_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1115_ = lean_string_length(v_word_1005_);
v___x_1116_ = lean_nat_mul(v_a_1006_, v___x_1115_);
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = lean_nat_mul(v___x_1116_, v___x_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_nat_mul(v___x_1113_, v___x_1117_);
lean_dec(v___x_1113_);
v___x_1120_ = lean_nat_add(v___x_1118_, v___x_1119_);
lean_dec(v___x_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(v___x_1114_);
v___x_1122_ = lean_array_get(v___x_1121_, v_fst_1017_, v___x_1120_);
lean_dec(v___x_1121_);
v___x_1123_ = lean_nat_add(v___x_1120_, v___x_1022_);
lean_dec(v___x_1120_);
v___x_1124_ = lean_box(v___x_1114_);
v___x_1125_ = lean_array_get(v___x_1124_, v_fst_1017_, v___x_1123_);
lean_dec(v___x_1123_);
lean_dec(v___x_1124_);
v___x_1126_ = lean_unbox(v___x_1122_);
v___x_1127_ = lean_unbox(v___x_1125_);
v___x_1128_ = lean_int16_dec_le(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
uint16_t v___x_1129_; 
lean_dec(v___x_1125_);
v___x_1129_ = lean_unbox(v___x_1122_);
lean_dec(v___x_1122_);
v___y_1053_ = v___x_1129_;
goto v___jp_1052_;
}
else
{
uint16_t v___x_1130_; 
lean_dec(v___x_1122_);
v___x_1130_ = lean_unbox(v___x_1125_);
lean_dec(v___x_1125_);
v___y_1053_ = v___x_1130_;
goto v___jp_1052_;
}
}
v___jp_1023_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_idx_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1027_ = lean_string_length(v_word_1005_);
v___x_1028_ = lean_nat_mul(v_a_1006_, v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(2u);
v___x_1030_ = lean_nat_mul(v___x_1028_, v___x_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_nat_mul(v_i_1013_, v___x_1029_);
v_idx_1032_ = lean_nat_add(v___x_1030_, v___x_1031_);
lean_dec(v___x_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(v___y_1024_);
v___x_1034_ = lean_array_set(v_fst_1017_, v_idx_1032_, v___x_1033_);
v___x_1035_ = lean_nat_add(v_idx_1032_, v___x_1022_);
lean_dec(v_idx_1032_);
v___x_1036_ = lean_box(v_matchScore_1026_);
v___x_1037_ = lean_array_set(v___x_1034_, v___x_1035_, v___x_1036_);
lean_dec(v___x_1035_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v_runLengths_1025_);
lean_ctor_set(v___x_1020_, 0, v___x_1037_);
v___x_1039_ = v___x_1020_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_runLengths_1025_);
v___x_1039_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_nat_add(v_i_1013_, v_step_1015_);
v___x_1041_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg(v_word_1005_, v_a_1006_, v_pattern_1007_, v_patternRoles_1008_, v_wordRoles_1009_, v___x_1010_, v___x_1004_, v_range_1011_, v___x_1039_, v___x_1040_);
return v___x_1041_;
}
}
v___jp_1043_:
{
uint16_t v___x_1047_; 
v___x_1047_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_1004_, v_i_1013_, v___y_1046_);
v___y_1024_ = v___y_1045_;
v_runLengths_1025_ = v___y_1044_;
v_matchScore_1026_ = v___x_1047_;
goto v___jp_1023_;
}
v___jp_1052_:
{
uint32_t v___x_1054_; uint32_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1054_ = lean_string_utf8_get(v_pattern_1007_, v_a_1006_);
v___x_1055_ = lean_string_utf8_get(v_word_1005_, v_i_1013_);
v___x_1056_ = lean_box(v___x_1048_);
v___x_1057_ = lean_array_get(v___x_1056_, v_patternRoles_1008_, v_a_1006_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_box(v___x_1048_);
v___x_1059_ = lean_array_get(v___x_1058_, v_wordRoles_1009_, v_i_1013_);
lean_dec(v___x_1058_);
v___x_1060_ = lean_unbox(v___x_1057_);
v___x_1061_ = lean_unbox(v___x_1059_);
v___x_1062_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_1054_, v___x_1055_, v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec(v___x_1059_);
lean_dec(v___x_1057_);
v___y_1024_ = v___y_1053_;
v_runLengths_1025_ = v_snd_1018_;
v_matchScore_1026_ = v_matchScore_1049_;
goto v___jp_1023_;
}
else
{
if (v___x_1051_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint16_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; uint8_t v___x_1070_; uint16_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint16_t v___x_1074_; uint16_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1063_ = lean_string_length(v_word_1005_);
v___x_1064_ = lean_nat_mul(v_a_1006_, v___x_1063_);
v___x_1065_ = lean_nat_add(v___x_1064_, v_i_1013_);
lean_dec(v___x_1064_);
v___x_1066_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1067_ = lean_box(v___x_1066_);
v___x_1068_ = lean_array_set(v_snd_1018_, v___x_1065_, v___x_1067_);
lean_dec(v___x_1065_);
v___x_1069_ = lean_unbox(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1070_ = lean_unbox(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1071_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_1007_, v_word_1005_, v_a_1006_, v_i_1013_, v___x_1069_, v___x_1070_, v_matchScore_1049_);
v___x_1072_ = lean_box(v___x_1050_);
v___x_1073_ = lean_array_get(v___x_1072_, v___x_1010_, v_i_1013_);
lean_dec(v___x_1072_);
v___x_1074_ = lean_unbox(v___x_1073_);
lean_dec(v___x_1073_);
v___x_1075_ = lean_int16_sub(v___x_1071_, v___x_1074_);
v___x_1076_ = lean_int16_dec_eq(v___x_1075_, v_matchScore_1049_);
if (v___x_1076_ == 0)
{
v___y_1024_ = v___y_1053_;
v_runLengths_1025_ = v___x_1068_;
v_matchScore_1026_ = v___x_1075_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1077_; uint16_t v___x_1078_; 
v___x_1077_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_1078_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_1077_);
v___y_1024_ = v___y_1053_;
v_runLengths_1025_ = v___x_1068_;
v_matchScore_1026_ = v___x_1078_;
goto v___jp_1023_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint16_t v___x_1086_; uint16_t v___x_1087_; uint16_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint16_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; uint16_t v___x_1102_; uint16_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; uint8_t v___x_1108_; uint16_t v___x_1109_; uint16_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1079_ = lean_nat_sub(v_a_1006_, v___x_1022_);
v___x_1080_ = lean_nat_sub(v_i_1013_, v___x_1022_);
v___x_1081_ = lean_string_length(v_word_1005_);
v___x_1082_ = lean_nat_mul(v___x_1079_, v___x_1081_);
lean_dec(v___x_1079_);
v___x_1083_ = lean_nat_add(v___x_1082_, v___x_1080_);
v___x_1084_ = lean_box(v___x_1050_);
v___x_1085_ = lean_array_get(v___x_1084_, v_snd_1018_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v___x_1084_);
v___x_1086_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1087_ = lean_unbox(v___x_1085_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_int16_add(v___x_1087_, v___x_1086_);
v___x_1089_ = lean_nat_mul(v_a_1006_, v___x_1081_);
v___x_1090_ = lean_nat_add(v___x_1089_, v_i_1013_);
lean_dec(v___x_1089_);
v___x_1091_ = lean_box(v___x_1088_);
v___x_1092_ = lean_array_set(v_snd_1018_, v___x_1090_, v___x_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1094_ = lean_unsigned_to_nat(2u);
v___x_1095_ = lean_nat_mul(v___x_1082_, v___x_1094_);
lean_dec(v___x_1082_);
v___x_1096_ = lean_nat_mul(v___x_1080_, v___x_1094_);
lean_dec(v___x_1080_);
v___x_1097_ = lean_nat_add(v___x_1095_, v___x_1096_);
lean_dec(v___x_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(v___x_1093_);
v___x_1099_ = lean_array_get(v___x_1098_, v_fst_1017_, v___x_1097_);
lean_dec(v___x_1098_);
v___x_1100_ = lean_unbox(v___x_1057_);
v___x_1101_ = lean_unbox(v___x_1059_);
v___x_1102_ = lean_unbox(v___x_1099_);
lean_dec(v___x_1099_);
v___x_1103_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_1007_, v_word_1005_, v_a_1006_, v_i_1013_, v___x_1100_, v___x_1101_, v___x_1010_, v___x_1102_);
v___x_1104_ = lean_nat_add(v___x_1097_, v___x_1022_);
lean_dec(v___x_1097_);
v___x_1105_ = lean_box(v___x_1093_);
v___x_1106_ = lean_array_get(v___x_1105_, v_fst_1017_, v___x_1104_);
lean_dec(v___x_1104_);
lean_dec(v___x_1105_);
v___x_1107_ = lean_unbox(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1108_ = lean_unbox(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1109_ = lean_unbox(v___x_1106_);
lean_dec(v___x_1106_);
v___x_1110_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_1007_, v_word_1005_, v_a_1006_, v_i_1013_, v___x_1107_, v___x_1108_, v___x_1088_, v___x_1109_);
v___x_1111_ = lean_int16_dec_le(v___x_1103_, v___x_1110_);
if (v___x_1111_ == 0)
{
v___y_1044_ = v___x_1092_;
v___y_1045_ = v___y_1053_;
v___y_1046_ = v___x_1103_;
goto v___jp_1043_;
}
else
{
v___y_1044_ = v___x_1092_;
v___y_1045_ = v___y_1053_;
v___y_1046_ = v___x_1110_;
goto v___jp_1043_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* v___x_1132_, lean_object* v_word_1133_, lean_object* v_a_1134_, lean_object* v_pattern_1135_, lean_object* v_patternRoles_1136_, lean_object* v_wordRoles_1137_, lean_object* v___x_1138_, lean_object* v_range_1139_, lean_object* v_b_1140_, lean_object* v_i_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v___x_1132_, v_word_1133_, v_a_1134_, v_pattern_1135_, v_patternRoles_1136_, v_wordRoles_1137_, v___x_1138_, v_range_1139_, v_b_1140_, v_i_1141_);
lean_dec(v_i_1141_);
lean_dec_ref(v_range_1139_);
lean_dec_ref(v___x_1138_);
lean_dec_ref(v_wordRoles_1137_);
lean_dec_ref(v_patternRoles_1136_);
lean_dec_ref(v_pattern_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_word_1133_);
lean_dec(v___x_1132_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v_word_1146_, lean_object* v_pattern_1147_, lean_object* v_patternRoles_1148_, lean_object* v_wordRoles_1149_, lean_object* v___x_1150_, lean_object* v_range_1151_, lean_object* v_b_1152_, lean_object* v_i_1153_){
_start:
{
lean_object* v_stop_1154_; lean_object* v_step_1155_; uint8_t v___x_1156_; 
v_stop_1154_ = lean_ctor_get(v_range_1151_, 1);
v_step_1155_ = lean_ctor_get(v_range_1151_, 2);
v___x_1156_ = lean_nat_dec_lt(v_i_1153_, v_stop_1154_);
if (v___x_1156_ == 0)
{
lean_dec(v_i_1153_);
return v_b_1152_;
}
else
{
lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1182_; 
v_fst_1157_ = lean_ctor_get(v_b_1152_, 0);
v_snd_1158_ = lean_ctor_get(v_b_1152_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_b_1152_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1160_ = v_b_1152_;
v_isShared_1161_ = v_isSharedCheck_1182_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_inc(v_fst_1157_);
lean_dec(v_b_1152_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1182_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_sub(v___x_1143_, v_i_1153_);
v___x_1164_ = lean_nat_sub(v___x_1163_, v___x_1162_);
lean_dec(v___x_1163_);
v___x_1165_ = lean_nat_sub(v___x_1144_, v___x_1164_);
lean_dec(v___x_1164_);
lean_inc(v_i_1153_);
v___x_1166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1166_, 0, v_i_1153_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
lean_ctor_set(v___x_1166_, 2, v___x_1162_);
if (v_isShared_1161_ == 0)
{
v___x_1168_ = v___x_1160_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_fst_1157_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_snd_1158_);
v___x_1168_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1180_; 
v___x_1169_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v___x_1145_, v_word_1146_, v_i_1153_, v_pattern_1147_, v_patternRoles_1148_, v_wordRoles_1149_, v___x_1150_, v___x_1166_, v___x_1168_, v_i_1153_);
lean_dec_ref_known(v___x_1166_, 3);
v_fst_1170_ = lean_ctor_get(v___x_1169_, 0);
v_snd_1171_ = lean_ctor_get(v___x_1169_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1173_ = v___x_1169_;
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v___x_1169_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_snd_1171_);
v___x_1176_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_nat_add(v_i_1153_, v_step_1155_);
lean_dec(v_i_1153_);
v_b_1152_ = v___x_1176_;
v_i_1153_ = v___x_1177_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* v___x_1183_, lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v_word_1186_, lean_object* v_pattern_1187_, lean_object* v_patternRoles_1188_, lean_object* v_wordRoles_1189_, lean_object* v___x_1190_, lean_object* v_range_1191_, lean_object* v_b_1192_, lean_object* v_i_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v___x_1183_, v___x_1184_, v___x_1185_, v_word_1186_, v_pattern_1187_, v_patternRoles_1188_, v_wordRoles_1189_, v___x_1190_, v_range_1191_, v_b_1192_, v_i_1193_);
lean_dec_ref(v_range_1191_);
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_wordRoles_1189_);
lean_dec_ref(v_patternRoles_1188_);
lean_dec_ref(v_pattern_1187_);
lean_dec_ref(v_word_1186_);
lean_dec(v___x_1185_);
lean_dec(v___x_1184_);
lean_dec(v___x_1183_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* v_wordRoles_1195_, lean_object* v_range_1196_, lean_object* v_b_1197_, lean_object* v_i_1198_){
_start:
{
lean_object* v_stop_1199_; lean_object* v_step_1200_; uint8_t v___x_1201_; 
v_stop_1199_ = lean_ctor_get(v_range_1196_, 1);
v_step_1200_ = lean_ctor_get(v_range_1196_, 2);
v___x_1201_ = lean_nat_dec_lt(v_i_1198_, v_stop_1199_);
if (v___x_1201_ == 0)
{
lean_dec(v_i_1198_);
return v_b_1197_;
}
else
{
lean_object* v_snd_1202_; lean_object* v_snd_1203_; lean_object* v_fst_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1260_; 
v_snd_1202_ = lean_ctor_get(v_b_1197_, 1);
lean_inc(v_snd_1202_);
v_snd_1203_ = lean_ctor_get(v_snd_1202_, 1);
lean_inc(v_snd_1203_);
v_fst_1204_ = lean_ctor_get(v_b_1197_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_b_1197_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_b_1197_, 1);
lean_dec(v_unused_1261_);
v___x_1206_ = v_b_1197_;
v_isShared_1207_ = v_isSharedCheck_1260_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_fst_1204_);
lean_dec(v_b_1197_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1260_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_fst_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1258_; 
v_fst_1208_ = lean_ctor_get(v_snd_1202_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_snd_1202_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_snd_1202_, 1);
lean_dec(v_unused_1259_);
v___x_1210_ = v_snd_1202_;
v_isShared_1211_ = v_isSharedCheck_1258_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_fst_1208_);
lean_dec(v_snd_1202_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1258_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_fst_1212_; lean_object* v_snd_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1257_; 
v_fst_1212_ = lean_ctor_get(v_snd_1203_, 0);
v_snd_1213_ = lean_ctor_get(v_snd_1203_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_snd_1203_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1215_ = v_snd_1203_;
v_isShared_1216_ = v_isSharedCheck_1257_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_snd_1213_);
lean_inc(v_fst_1212_);
lean_dec(v_snd_1203_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1257_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
uint8_t v___x_1217_; lean_object* v_lastSepIdx_1218_; lean_object* v_lastSepIdx_1220_; uint16_t v_penaltyNs_1221_; uint16_t v_penaltySkip_1222_; uint8_t v___x_1245_; 
v___x_1217_ = 0;
v_lastSepIdx_1218_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_nat_dec_eq(v_i_1198_, v_lastSepIdx_1218_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = lean_box(v___x_1217_);
v___x_1247_ = lean_array_get(v___x_1246_, v_wordRoles_1195_, v_i_1198_);
lean_dec(v___x_1246_);
v___x_1248_ = lean_unbox(v___x_1247_);
lean_dec(v___x_1247_);
if (v___x_1248_ == 2)
{
uint16_t v_penaltyNs_1249_; uint16_t v___x_1250_; uint16_t v___x_1251_; uint16_t v___x_1252_; 
lean_dec(v_snd_1213_);
lean_dec(v_fst_1208_);
v_penaltyNs_1249_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1250_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1251_ = lean_unbox(v_fst_1212_);
lean_dec(v_fst_1212_);
v___x_1252_ = lean_int16_add(v___x_1251_, v___x_1250_);
lean_inc(v_i_1198_);
v_lastSepIdx_1220_ = v_i_1198_;
v_penaltyNs_1221_ = v___x_1252_;
v_penaltySkip_1222_ = v_penaltyNs_1249_;
goto v___jp_1219_;
}
else
{
uint16_t v___x_1253_; uint16_t v___x_1254_; 
v___x_1253_ = lean_unbox(v_fst_1212_);
lean_dec(v_fst_1212_);
v___x_1254_ = lean_unbox(v_snd_1213_);
lean_dec(v_snd_1213_);
v_lastSepIdx_1220_ = v_fst_1208_;
v_penaltyNs_1221_ = v___x_1253_;
v_penaltySkip_1222_ = v___x_1254_;
goto v___jp_1219_;
}
}
else
{
uint16_t v___x_1255_; uint16_t v___x_1256_; 
v___x_1255_ = lean_unbox(v_fst_1212_);
lean_dec(v_fst_1212_);
v___x_1256_ = lean_unbox(v_snd_1213_);
lean_dec(v_snd_1213_);
v_lastSepIdx_1220_ = v_fst_1208_;
v_penaltyNs_1221_ = v___x_1255_;
v_penaltySkip_1222_ = v___x_1256_;
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; uint8_t v___x_1226_; uint16_t v___x_1227_; uint16_t v___x_1228_; uint16_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1223_ = lean_box(v___x_1217_);
v___x_1224_ = lean_array_get(v___x_1223_, v_wordRoles_1195_, v_i_1198_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_nat_dec_eq(v_i_1198_, v_lastSepIdx_1218_);
v___x_1226_ = lean_unbox(v___x_1224_);
lean_dec(v___x_1224_);
v___x_1227_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_1226_, v___x_1225_);
v___x_1228_ = lean_int16_add(v_penaltySkip_1222_, v___x_1227_);
v___x_1229_ = lean_int16_add(v___x_1228_, v_penaltyNs_1221_);
v___x_1230_ = lean_box(v___x_1229_);
v___x_1231_ = lean_array_set(v_fst_1204_, v_i_1198_, v___x_1230_);
v___x_1232_ = lean_box(v_penaltyNs_1221_);
v___x_1233_ = lean_box(v___x_1228_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1233_);
lean_ctor_set(v___x_1215_, 0, v___x_1232_);
v___x_1235_ = v___x_1215_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1235_);
lean_ctor_set(v___x_1210_, 0, v_lastSepIdx_1220_);
v___x_1237_ = v___x_1210_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_lastSepIdx_1220_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1237_);
lean_ctor_set(v___x_1206_, 0, v___x_1231_);
v___x_1239_ = v___x_1206_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_nat_add(v_i_1198_, v_step_1200_);
lean_dec(v_i_1198_);
v_b_1197_ = v___x_1239_;
v_i_1198_ = v___x_1240_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* v_wordRoles_1262_, lean_object* v_range_1263_, lean_object* v_b_1264_, lean_object* v_i_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1262_, v_range_1263_, v_b_1264_, v_i_1265_);
lean_dec_ref(v_range_1263_);
lean_dec_ref(v_wordRoles_1262_);
return v_res_1266_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0(void){
_start:
{
uint16_t v_penaltyNs_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_penaltyNs_1267_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1268_ = lean_box(v_penaltyNs_1267_);
v___x_1269_ = lean_box(v_penaltyNs_1267_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1(void){
_start:
{
lean_object* v___x_1271_; lean_object* v_lastSepIdx_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
v_lastSepIdx_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_lastSepIdx_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* v_pattern_1274_, lean_object* v_word_1275_, lean_object* v_patternRoles_1276_, lean_object* v_wordRoles_1277_){
_start:
{
uint16_t v___y_1279_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_lastSepIdx_1290_; uint16_t v_penaltyNs_1291_; lean_object* v___x_1292_; lean_object* v_runLengths_1293_; lean_object* v___x_1294_; lean_object* v_startPenalties_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_snd_1301_; lean_object* v_fst_1302_; lean_object* v_fst_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1333_; 
v___x_1285_ = lean_string_length(v_pattern_1274_);
v___x_1286_ = lean_string_length(v_word_1275_);
v___x_1287_ = lean_nat_mul(v___x_1285_, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(2u);
v___x_1289_ = lean_nat_mul(v___x_1287_, v___x_1288_);
v_lastSepIdx_1290_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1291_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1292_ = lean_box(v_penaltyNs_1291_);
v_runLengths_1293_ = lean_mk_array(v___x_1287_, v___x_1292_);
v___x_1294_ = lean_box(v_penaltyNs_1291_);
v_startPenalties_1295_ = lean_mk_array(v___x_1286_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1297_, 0, v_lastSepIdx_1290_);
lean_ctor_set(v___x_1297_, 1, v___x_1286_);
lean_ctor_set(v___x_1297_, 2, v___x_1296_);
v___x_1298_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_startPenalties_1295_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1277_, v___x_1297_, v___x_1299_, v_lastSepIdx_1290_);
lean_dec_ref_known(v___x_1297_, 3);
v_snd_1301_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1301_);
v_fst_1302_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_fst_1302_);
lean_dec_ref(v___x_1300_);
v_fst_1303_ = lean_ctor_get(v_snd_1301_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_snd_1301_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_snd_1301_, 1);
lean_dec(v_unused_1334_);
v___x_1305_ = v_snd_1301_;
v_isShared_1306_ = v_isSharedCheck_1333_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_fst_1303_);
lean_dec(v_snd_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1333_;
goto v_resetjp_1304_;
}
v___jp_1278_:
{
uint16_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1281_ = lean_int16_dec_le(v___y_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_int16_to_int(v___y_1279_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
}
v_resetjp_1304_:
{
uint16_t v_matchScore_1307_; lean_object* v___x_1308_; lean_object* v_result_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v_matchScore_1307_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1308_ = lean_box(v_matchScore_1307_);
v_result_1309_ = lean_mk_array(v___x_1289_, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v_lastSepIdx_1290_);
lean_ctor_set(v___x_1310_, 1, v___x_1285_);
lean_ctor_set(v___x_1310_, 2, v___x_1296_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 1, v_runLengths_1293_);
lean_ctor_set(v___x_1305_, 0, v_result_1309_);
v___x_1312_ = v___x_1305_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_result_1309_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_runLengths_1293_);
v___x_1312_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v_fst_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint16_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint16_t v___x_1327_; uint16_t v___x_1328_; uint8_t v___x_1329_; 
v___x_1313_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v___x_1285_, v___x_1286_, v_fst_1303_, v_word_1275_, v_pattern_1274_, v_patternRoles_1276_, v_wordRoles_1277_, v_fst_1302_, v___x_1310_, v___x_1312_, v_lastSepIdx_1290_);
lean_dec_ref_known(v___x_1310_, 3);
lean_dec(v_fst_1302_);
lean_dec(v_fst_1303_);
v_fst_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_fst_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_nat_sub(v___x_1285_, v___x_1296_);
v___x_1316_ = lean_nat_sub(v___x_1286_, v___x_1296_);
v___x_1317_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1318_ = lean_nat_mul(v___x_1315_, v___x_1286_);
lean_dec(v___x_1315_);
v___x_1319_ = lean_nat_mul(v___x_1318_, v___x_1288_);
lean_dec(v___x_1318_);
v___x_1320_ = lean_nat_mul(v___x_1316_, v___x_1288_);
lean_dec(v___x_1316_);
v___x_1321_ = lean_nat_add(v___x_1319_, v___x_1320_);
lean_dec(v___x_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(v___x_1317_);
v___x_1323_ = lean_array_get(v___x_1322_, v_fst_1314_, v___x_1321_);
lean_dec(v___x_1322_);
v___x_1324_ = lean_nat_add(v___x_1321_, v___x_1296_);
lean_dec(v___x_1321_);
v___x_1325_ = lean_box(v___x_1317_);
v___x_1326_ = lean_array_get(v___x_1325_, v_fst_1314_, v___x_1324_);
lean_dec(v___x_1324_);
lean_dec(v_fst_1314_);
lean_dec(v___x_1325_);
v___x_1327_ = lean_unbox(v___x_1323_);
v___x_1328_ = lean_unbox(v___x_1326_);
v___x_1329_ = lean_int16_dec_le(v___x_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
uint16_t v___x_1330_; 
lean_dec(v___x_1326_);
v___x_1330_ = lean_unbox(v___x_1323_);
lean_dec(v___x_1323_);
v___y_1279_ = v___x_1330_;
goto v___jp_1278_;
}
else
{
uint16_t v___x_1331_; 
lean_dec(v___x_1323_);
v___x_1331_ = lean_unbox(v___x_1326_);
lean_dec(v___x_1326_);
v___y_1279_ = v___x_1331_;
goto v___jp_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* v_pattern_1335_, lean_object* v_word_1336_, lean_object* v_patternRoles_1337_, lean_object* v_wordRoles_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1335_, v_word_1336_, v_patternRoles_1337_, v_wordRoles_1338_);
lean_dec_ref(v_wordRoles_1338_);
lean_dec_ref(v_patternRoles_1337_);
lean_dec_ref(v_word_1336_);
lean_dec_ref(v_pattern_1335_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* v_wordRoles_1340_, lean_object* v_range_1341_, lean_object* v_b_1342_, lean_object* v_i_1343_, lean_object* v_hs_1344_, lean_object* v_hl_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1340_, v_range_1341_, v_b_1342_, v_i_1343_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* v_wordRoles_1347_, lean_object* v_range_1348_, lean_object* v_b_1349_, lean_object* v_i_1350_, lean_object* v_hs_1351_, lean_object* v_hl_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_1347_, v_range_1348_, v_b_1349_, v_i_1350_, v_hs_1351_, v_hl_1352_);
lean_dec_ref(v_range_1348_);
lean_dec_ref(v_wordRoles_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* v___x_1354_, lean_object* v_word_1355_, lean_object* v_a_1356_, lean_object* v_pattern_1357_, lean_object* v_patternRoles_1358_, lean_object* v_wordRoles_1359_, lean_object* v___x_1360_, lean_object* v_range_1361_, lean_object* v_b_1362_, lean_object* v_i_1363_, lean_object* v_hs_1364_, lean_object* v_hl_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v___x_1354_, v_word_1355_, v_a_1356_, v_pattern_1357_, v_patternRoles_1358_, v_wordRoles_1359_, v___x_1360_, v_range_1361_, v_b_1362_, v_i_1363_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* v___x_1367_, lean_object* v_word_1368_, lean_object* v_a_1369_, lean_object* v_pattern_1370_, lean_object* v_patternRoles_1371_, lean_object* v_wordRoles_1372_, lean_object* v___x_1373_, lean_object* v_range_1374_, lean_object* v_b_1375_, lean_object* v_i_1376_, lean_object* v_hs_1377_, lean_object* v_hl_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v___x_1367_, v_word_1368_, v_a_1369_, v_pattern_1370_, v_patternRoles_1371_, v_wordRoles_1372_, v___x_1373_, v_range_1374_, v_b_1375_, v_i_1376_, v_hs_1377_, v_hl_1378_);
lean_dec(v_i_1376_);
lean_dec_ref(v_range_1374_);
lean_dec_ref(v___x_1373_);
lean_dec_ref(v_wordRoles_1372_);
lean_dec_ref(v_patternRoles_1371_);
lean_dec_ref(v_pattern_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_word_1368_);
lean_dec(v___x_1367_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v_word_1383_, lean_object* v_pattern_1384_, lean_object* v_patternRoles_1385_, lean_object* v_wordRoles_1386_, lean_object* v___x_1387_, lean_object* v_range_1388_, lean_object* v_b_1389_, lean_object* v_i_1390_, lean_object* v_hs_1391_, lean_object* v_hl_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v___x_1380_, v___x_1381_, v___x_1382_, v_word_1383_, v_pattern_1384_, v_patternRoles_1385_, v_wordRoles_1386_, v___x_1387_, v_range_1388_, v_b_1389_, v_i_1390_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v_word_1397_, lean_object* v_pattern_1398_, lean_object* v_patternRoles_1399_, lean_object* v_wordRoles_1400_, lean_object* v___x_1401_, lean_object* v_range_1402_, lean_object* v_b_1403_, lean_object* v_i_1404_, lean_object* v_hs_1405_, lean_object* v_hl_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v___x_1394_, v___x_1395_, v___x_1396_, v_word_1397_, v_pattern_1398_, v_patternRoles_1399_, v_wordRoles_1400_, v___x_1401_, v_range_1402_, v_b_1403_, v_i_1404_, v_hs_1405_, v_hl_1406_);
lean_dec_ref(v_range_1402_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v_wordRoles_1400_);
lean_dec_ref(v_patternRoles_1399_);
lean_dec_ref(v_pattern_1398_);
lean_dec_ref(v_word_1397_);
lean_dec(v___x_1396_);
lean_dec(v___x_1395_);
lean_dec(v___x_1394_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5(lean_object* v_word_1408_, lean_object* v_a_1409_, lean_object* v_pattern_1410_, lean_object* v_patternRoles_1411_, lean_object* v_wordRoles_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v_range_1415_, lean_object* v_b_1416_, lean_object* v_i_1417_, lean_object* v_hs_1418_, lean_object* v_hl_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___redArg(v_word_1408_, v_a_1409_, v_pattern_1410_, v_patternRoles_1411_, v_wordRoles_1412_, v___x_1413_, v___x_1414_, v_range_1415_, v_b_1416_, v_i_1417_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5___boxed(lean_object* v_word_1421_, lean_object* v_a_1422_, lean_object* v_pattern_1423_, lean_object* v_patternRoles_1424_, lean_object* v_wordRoles_1425_, lean_object* v___x_1426_, lean_object* v___x_1427_, lean_object* v_range_1428_, lean_object* v_b_1429_, lean_object* v_i_1430_, lean_object* v_hs_1431_, lean_object* v_hl_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5_spec__5(v_word_1421_, v_a_1422_, v_pattern_1423_, v_patternRoles_1424_, v_wordRoles_1425_, v___x_1426_, v___x_1427_, v_range_1428_, v_b_1429_, v_i_1430_, v_hs_1431_, v_hl_1432_);
lean_dec_ref(v_range_1428_);
lean_dec(v___x_1427_);
lean_dec_ref(v___x_1426_);
lean_dec_ref(v_wordRoles_1425_);
lean_dec_ref(v_patternRoles_1424_);
lean_dec_ref(v_pattern_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_word_1421_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_nat_to_int(v_a_1434_);
return v___x_1435_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1436_; double v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_float_of_nat(v___x_1436_);
return v___x_1437_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1(void){
_start:
{
lean_object* v___x_1438_; double v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_float_of_nat(v___x_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_unsigned_to_nat(2u);
v___x_1441_ = lean_nat_to_int(v___x_1440_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1(void){
_start:
{
double v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1443_ = lean_box_float(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* v_pattern_1446_, lean_object* v_word_1447_){
_start:
{
double v___y_1449_; double v___y_1450_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = lean_string_utf8_byte_size(v_pattern_1446_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_nat_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_score_1462_; uint8_t v___x_1478_; 
v___x_1459_ = lean_string_length(v_word_1447_);
v___x_1460_ = lean_string_length(v_pattern_1446_);
v___x_1478_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_String_charactersIn(v_pattern_1446_, v_word_1447_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_box(0);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_1446_);
v___x_1482_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_1447_);
v___x_1483_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1446_, v_word_1447_, v___x_1481_, v___x_1482_);
lean_dec_ref(v___x_1482_);
lean_dec_ref(v___x_1481_);
if (lean_obj_tag(v___x_1483_) == 1)
{
lean_object* v_val_1484_; uint8_t v___x_1485_; 
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = lean_nat_dec_eq(v___x_1460_, v___x_1459_);
if (v___x_1485_ == 0)
{
v_score_1462_ = v_val_1484_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1486_; lean_object* v_score_1487_; 
v___x_1486_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
v_score_1487_ = lean_int_mul(v_val_1484_, v___x_1486_);
lean_dec(v_val_1484_);
v_score_1462_ = v_score_1487_;
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1488_; 
lean_dec(v___x_1483_);
v___x_1488_ = lean_box(0);
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
v___jp_1461_:
{
lean_object* v_perfect_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_perfectMatch_1470_; double v___x_1471_; lean_object* v___x_1472_; double v___x_1473_; double v_normScore_1474_; double v___x_1475_; double v___x_1476_; uint8_t v___x_1477_; 
v_perfect_1463_ = lean_unsigned_to_nat(4u);
v___x_1464_ = lean_nat_mul(v_perfect_1463_, v___x_1460_);
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v___x_1460_, v___x_1465_);
v___x_1467_ = lean_nat_mul(v___x_1460_, v___x_1466_);
lean_dec(v___x_1466_);
v___x_1468_ = lean_nat_shiftr(v___x_1467_, v___x_1465_);
lean_dec(v___x_1467_);
v___x_1469_ = lean_nat_sub(v___x_1468_, v___x_1465_);
lean_dec(v___x_1468_);
v_perfectMatch_1470_ = lean_nat_add(v___x_1464_, v___x_1469_);
lean_dec(v___x_1469_);
lean_dec(v___x_1464_);
v___x_1471_ = l_Float_ofInt(v_score_1462_);
lean_dec(v_score_1462_);
v___x_1472_ = lean_nat_to_int(v_perfectMatch_1470_);
v___x_1473_ = l_Float_ofInt(v___x_1472_);
lean_dec(v___x_1472_);
v_normScore_1474_ = lean_float_div(v___x_1471_, v___x_1473_);
v___x_1475_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1476_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1);
v___x_1477_ = lean_float_decLe(v___x_1476_, v_normScore_1474_);
if (v___x_1477_ == 0)
{
v___y_1449_ = v___x_1475_;
v___y_1450_ = v___x_1476_;
goto v___jp_1448_;
}
else
{
v___y_1449_ = v___x_1475_;
v___y_1450_ = v_normScore_1474_;
goto v___jp_1448_;
}
}
}
else
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return v___x_1490_;
}
v___jp_1448_:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_float_decLe(v___y_1449_, v___y_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_box_float(v___y_1450_);
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_box_float(v___y_1449_);
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* v_pattern_1491_, lean_object* v_word_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1491_, v_word_1492_);
lean_dec_ref(v_word_1492_);
lean_dec_ref(v_pattern_1491_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* v_pattern_1494_, lean_object* v_word_1495_, double v_threshold_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1494_, v_word_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
return v___x_1497_;
}
else
{
lean_object* v_val_1498_; double v___x_1499_; uint8_t v___x_1500_; 
v_val_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1498_);
v___x_1499_ = lean_unbox_float(v_val_1498_);
lean_dec(v_val_1498_);
v___x_1500_ = lean_float_decLt(v_threshold_1496_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec_ref_known(v___x_1497_, 1);
v___x_1501_ = lean_box(0);
return v___x_1501_;
}
else
{
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* v_pattern_1502_, lean_object* v_word_1503_, lean_object* v_threshold_1504_){
_start:
{
double v_threshold_boxed_1505_; lean_object* v_res_1506_; 
v_threshold_boxed_1505_ = lean_unbox_float(v_threshold_1504_);
lean_dec_ref(v_threshold_1504_);
v_res_1506_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1502_, v_word_1503_, v_threshold_boxed_1505_);
lean_dec_ref(v_word_1503_);
lean_dec_ref(v_pattern_1502_);
return v_res_1506_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* v_pattern_1507_, lean_object* v_word_1508_, double v_threshold_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1507_, v_word_1508_, v_threshold_1509_);
if (lean_obj_tag(v___x_1510_) == 0)
{
uint8_t v___x_1511_; 
v___x_1511_ = 0;
return v___x_1511_;
}
else
{
uint8_t v___x_1512_; 
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = 1;
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* v_pattern_1513_, lean_object* v_word_1514_, lean_object* v_threshold_1515_){
_start:
{
double v_threshold_boxed_1516_; uint8_t v_res_1517_; lean_object* v_r_1518_; 
v_threshold_boxed_1516_ = lean_unbox_float(v_threshold_1515_);
lean_dec_ref(v_threshold_1515_);
v_res_1517_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1513_, v_word_1514_, v_threshold_boxed_1516_);
lean_dec_ref(v_word_1514_);
lean_dec_ref(v_pattern_1513_);
v_r_1518_ = lean_box(v_res_1517_);
return v_r_1518_;
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
