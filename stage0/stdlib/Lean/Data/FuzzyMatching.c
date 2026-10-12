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
extern uint16_t l_instInhabitedInt16;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
double l_Float_ofInt(lean_object*);
double lean_float_div(double, double);
double lean_float_maximum(double, double);
double lean_float_minimum(double, double);
uint8_t l_Lean_String_charactersIn(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___impl___boxed(lean_object*);
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
uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(lean_object* v_a_92_, lean_object* v_b_93_, lean_object* v_aPos_94_, lean_object* v_bPos_95_){
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
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_92_ = stack[0].m_obj;
lean_object* v_b_93_ = stack[1].m_obj;
lean_object* v_aPos_94_ = stack[2].m_obj;
lean_object* v_bPos_95_ = stack[3].m_obj;
uint8_t v_res_122_;
v_res_122_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_92_, v_b_93_, v_aPos_94_, v_bPos_95_);
stack->m_num = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go___boxed(lean_object* v_a_123_, lean_object* v_b_124_, lean_object* v_aPos_125_, lean_object* v_bPos_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_123_, v_b_124_, v_aPos_125_, v_bPos_126_);
lean_dec_ref(v_b_124_);
lean_dec_ref(v_a_123_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(v_a_129_, v_b_130_, v___x_131_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_129_ = stack[0].m_obj;
lean_object* v_b_130_ = stack[1].m_obj;
uint8_t v_res_133_;
v_res_133_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(v_a_129_, v_b_130_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower___boxed(lean_object* v_a_134_, lean_object* v_b_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(v_a_134_, v_b_135_);
lean_dec_ref(v_b_135_);
lean_dec_ref(v_a_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___impl(uint8_t v_x_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_box(v_x_138_);
v___x_140_ = lean_obj_tag_nat(v___x_139_);
lean_dec(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharType_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_138_ = stack[0].m_num;
lean_object* v_res_141_;
v_res_141_ = l_Lean_FuzzyMatching_CharType_ctorIdx___impl(v_x_138_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___impl___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_x_4__boxed_143_; lean_object* v_res_144_; 
v_x_4__boxed_143_ = lean_unbox(v_x_142_);
v_res_144_ = l_Lean_FuzzyMatching_CharType_ctorIdx___impl(v_x_4__boxed_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg(lean_object* v_k_145_){
_start:
{
lean_inc(v_k_145_);
return v_k_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_FuzzyMatching_CharType_ctorElim___redArg(v_k_146_);
lean_dec(v_k_146_);
return v_res_147_;
}
}
lean_object* l_Lean_FuzzyMatching_CharType_ctorElim(lean_object* v_motive_148_, lean_object* v_ctorIdx_149_, uint8_t v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
lean_inc(v_k_152_);
return v_k_152_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharType_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_149_ = stack[1].m_obj;
uint8_t v_t_150_ = stack[2].m_num;
lean_object* v_k_152_ = stack[4].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_FuzzyMatching_CharType_ctorElim(lean_box(0), v_ctorIdx_149_, v_t_150_, lean_box(0), v_k_152_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___boxed(lean_object* v_motive_154_, lean_object* v_ctorIdx_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_k_158_){
_start:
{
uint8_t v_t_boxed_159_; lean_object* v_res_160_; 
v_t_boxed_159_ = lean_unbox(v_t_156_);
v_res_160_ = l_Lean_FuzzyMatching_CharType_ctorElim(v_motive_154_, v_ctorIdx_155_, v_t_boxed_159_, v_h_157_, v_k_158_);
lean_dec(v_k_158_);
lean_dec(v_ctorIdx_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg(lean_object* v_lower_161_){
_start:
{
lean_inc(v_lower_161_);
return v_lower_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(lean_object* v_lower_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_FuzzyMatching_CharType_lower_elim___redArg(v_lower_162_);
lean_dec(v_lower_162_);
return v_res_163_;
}
}
lean_object* l_Lean_FuzzyMatching_CharType_lower_elim(lean_object* v_motive_164_, uint8_t v_t_165_, lean_object* v_h_166_, lean_object* v_lower_167_){
_start:
{
lean_inc(v_lower_167_);
return v_lower_167_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharType_lower_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_165_ = stack[1].m_num;
lean_object* v_lower_167_ = stack[3].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_FuzzyMatching_CharType_lower_elim(lean_box(0), v_t_165_, lean_box(0), v_lower_167_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___boxed(lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_lower_172_){
_start:
{
uint8_t v_t_boxed_173_; lean_object* v_res_174_; 
v_t_boxed_173_ = lean_unbox(v_t_170_);
v_res_174_ = l_Lean_FuzzyMatching_CharType_lower_elim(v_motive_169_, v_t_boxed_173_, v_h_171_, v_lower_172_);
lean_dec(v_lower_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg(lean_object* v_upper_175_){
_start:
{
lean_inc(v_upper_175_);
return v_upper_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(lean_object* v_upper_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_FuzzyMatching_CharType_upper_elim___redArg(v_upper_176_);
lean_dec(v_upper_176_);
return v_res_177_;
}
}
lean_object* l_Lean_FuzzyMatching_CharType_upper_elim(lean_object* v_motive_178_, uint8_t v_t_179_, lean_object* v_h_180_, lean_object* v_upper_181_){
_start:
{
lean_inc(v_upper_181_);
return v_upper_181_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharType_upper_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_179_ = stack[1].m_num;
lean_object* v_upper_181_ = stack[3].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_Lean_FuzzyMatching_CharType_upper_elim(lean_box(0), v_t_179_, lean_box(0), v_upper_181_);
stack->m_obj
 = v_res_182_;
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
lean_object* l_Lean_FuzzyMatching_CharType_separator_elim(lean_object* v_motive_192_, uint8_t v_t_193_, lean_object* v_h_194_, lean_object* v_separator_195_){
_start:
{
lean_inc(v_separator_195_);
return v_separator_195_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharType_separator_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_193_ = stack[1].m_num;
lean_object* v_separator_195_ = stack[3].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Lean_FuzzyMatching_CharType_separator_elim(lean_box(0), v_t_193_, lean_box(0), v_separator_195_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_separator_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lean_FuzzyMatching_CharType_separator_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_separator_200_);
lean_dec(v_separator_200_);
return v_res_202_;
}
}
uint8_t l_Lean_FuzzyMatching_charType(uint32_t v_c_203_){
_start:
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 65;
v___x_225_ = lean_uint32_dec_le(v___x_224_, v_c_203_);
if (v___x_225_ == 0)
{
goto v___jp_219_;
}
else
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 90;
v___x_227_ = lean_uint32_dec_le(v_c_203_, v___x_226_);
if (v___x_227_ == 0)
{
goto v___jp_219_;
}
else
{
goto v___jp_204_;
}
}
v___jp_204_:
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 65;
v___x_206_ = lean_uint32_dec_le(v___x_205_, v_c_203_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
else
{
uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_208_ = 90;
v___x_209_ = lean_uint32_dec_le(v_c_203_, v___x_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
v___x_210_ = 0;
return v___x_210_;
}
else
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
}
}
v___jp_212_:
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 48;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v_c_203_);
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
v___x_217_ = lean_uint32_dec_le(v_c_203_, v___x_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 2;
return v___x_218_;
}
else
{
goto v___jp_204_;
}
}
}
v___jp_219_:
{
uint32_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = 97;
v___x_221_ = lean_uint32_dec_le(v___x_220_, v_c_203_);
if (v___x_221_ == 0)
{
goto v___jp_212_;
}
else
{
uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 122;
v___x_223_ = lean_uint32_dec_le(v_c_203_, v___x_222_);
if (v___x_223_ == 0)
{
goto v___jp_212_;
}
else
{
goto v___jp_204_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_charType_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_203_ = stack[0].m_num;
uint8_t v_res_228_;
v_res_228_ = l_Lean_FuzzyMatching_charType(v_c_203_);
stack->m_num = v_res_228_;
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
lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___impl(uint8_t v_x_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_box(v_x_233_);
v___x_235_ = lean_obj_tag_nat(v___x_234_);
lean_dec(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharRole_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_233_ = stack[0].m_num;
lean_object* v_res_236_;
v_res_236_ = l_Lean_FuzzyMatching_CharRole_ctorIdx___impl(v_x_233_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___impl___boxed(lean_object* v_x_237_){
_start:
{
uint8_t v_x_4__boxed_238_; lean_object* v_res_239_; 
v_x_4__boxed_238_ = lean_unbox(v_x_237_);
v_res_239_ = l_Lean_FuzzyMatching_CharRole_ctorIdx___impl(v_x_4__boxed_238_);
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
lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, uint8_t v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
lean_inc(v_k_247_);
return v_k_247_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharRole_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_244_ = stack[1].m_obj;
uint8_t v_t_245_ = stack[2].m_num;
lean_object* v_k_247_ = stack[4].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_FuzzyMatching_CharRole_ctorElim(lean_box(0), v_ctorIdx_244_, v_t_245_, lean_box(0), v_k_247_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_FuzzyMatching_CharRole_ctorElim(v_motive_249_, v_ctorIdx_250_, v_t_boxed_254_, v_h_252_, v_k_253_);
lean_dec(v_k_253_);
lean_dec(v_ctorIdx_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object* v_head_256_){
_start:
{
lean_inc(v_head_256_);
return v_head_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object* v_head_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(v_head_257_);
lean_dec(v_head_257_);
return v_res_258_;
}
}
lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_head_262_){
_start:
{
lean_inc(v_head_262_);
return v_head_262_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharRole_head_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_260_ = stack[1].m_num;
lean_object* v_head_262_ = stack[3].m_obj;
lean_object* v_res_263_;
v_res_263_ = l_Lean_FuzzyMatching_CharRole_head_elim(lean_box(0), v_t_260_, lean_box(0), v_head_262_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_head_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_FuzzyMatching_CharRole_head_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_head_267_);
lean_dec(v_head_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object* v_tail_270_){
_start:
{
lean_inc(v_tail_270_);
return v_tail_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object* v_tail_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(v_tail_271_);
lean_dec(v_tail_271_);
return v_res_272_;
}
}
lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_tail_276_){
_start:
{
lean_inc(v_tail_276_);
return v_tail_276_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharRole_tail_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_274_ = stack[1].m_num;
lean_object* v_tail_276_ = stack[3].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_FuzzyMatching_CharRole_tail_elim(lean_box(0), v_t_274_, lean_box(0), v_tail_276_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_tail_281_){
_start:
{
uint8_t v_t_boxed_282_; lean_object* v_res_283_; 
v_t_boxed_282_ = lean_unbox(v_t_279_);
v_res_283_ = l_Lean_FuzzyMatching_CharRole_tail_elim(v_motive_278_, v_t_boxed_282_, v_h_280_, v_tail_281_);
lean_dec(v_tail_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object* v_separator_284_){
_start:
{
lean_inc(v_separator_284_);
return v_separator_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object* v_separator_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(v_separator_285_);
lean_dec(v_separator_285_);
return v_res_286_;
}
}
lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object* v_motive_287_, uint8_t v_t_288_, lean_object* v_h_289_, lean_object* v_separator_290_){
_start:
{
lean_inc(v_separator_290_);
return v_separator_290_;
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_CharRole_separator_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_288_ = stack[1].m_num;
lean_object* v_separator_290_ = stack[3].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_FuzzyMatching_CharRole_separator_elim(lean_box(0), v_t_288_, lean_box(0), v_separator_290_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_separator_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_FuzzyMatching_CharRole_separator_elim(v_motive_292_, v_t_boxed_296_, v_h_294_, v_separator_295_);
lean_dec(v_separator_295_);
return v_res_297_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default(void){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole(void){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
}
uint8_t l_Lean_FuzzyMatching_charRole(lean_object* v_prev_x3f_300_, uint8_t v_curr_301_, lean_object* v_next_x3f_302_){
_start:
{
if (v_curr_301_ == 2)
{
uint8_t v___x_303_; 
v___x_303_ = 2;
return v___x_303_;
}
else
{
if (lean_obj_tag(v_prev_x3f_300_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
else
{
lean_object* v_val_305_; uint8_t v___x_306_; 
v_val_305_ = lean_ctor_get(v_prev_x3f_300_, 0);
v___x_306_ = lean_unbox(v_val_305_);
if (v___x_306_ == 2)
{
uint8_t v___x_307_; 
v___x_307_ = 0;
return v___x_307_;
}
else
{
if (v_curr_301_ == 0)
{
uint8_t v___x_308_; 
v___x_308_ = 1;
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = lean_unbox(v_val_305_);
if (v___x_309_ == 1)
{
if (lean_obj_tag(v_next_x3f_302_) == 1)
{
lean_object* v_val_310_; uint8_t v___x_311_; 
v_val_310_ = lean_ctor_get(v_next_x3f_302_, 0);
v___x_311_ = lean_unbox(v_val_310_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 1;
return v___x_313_;
}
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
v___x_315_ = 0;
return v___x_315_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_charRole_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_x3f_300_ = stack[0].m_obj;
uint8_t v_curr_301_ = stack[1].m_num;
lean_object* v_next_x3f_302_ = stack[2].m_obj;
uint8_t v_res_316_;
v_res_316_ = l_Lean_FuzzyMatching_charRole(v_prev_x3f_300_, v_curr_301_, v_next_x3f_302_);
stack->m_num = v_res_316_;
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
uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object* v_prev_x3f_391_, uint32_t v_curr_392_, lean_object* v_next_x3f_393_){
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
lean_dec_ref_known(v___y_395_, 1);
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
lean_dec_ref_known(v___y_397_, 1);
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
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_x3f_391_ = stack[0].m_obj;
uint32_t v_curr_392_ = stack[1].m_num;
lean_object* v_next_x3f_393_ = stack[2].m_obj;
uint8_t v_res_438_;
v_res_438_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_391_, v_curr_392_, v_next_x3f_393_);
stack->m_num = v_res_438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* v_prev_x3f_439_, lean_object* v_curr_440_, lean_object* v_next_x3f_441_){
_start:
{
uint32_t v_curr_boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_curr_boxed_442_ = lean_unbox_uint32(v_curr_440_);
lean_dec(v_curr_440_);
v_res_443_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_439_, v_curr_boxed_442_, v_next_x3f_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* v_string_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_string_utf8_byte_size(v_string_447_);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_nat_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_string_length(v_string_447_);
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v_result_454_; lean_object* v___x_455_; uint32_t v___x_456_; uint32_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v_result_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint32_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint32_t v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_result_454_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_string_utf8_get(v_string_447_, v___x_449_);
v___x_457_ = lean_string_utf8_get(v_string_447_, v___x_452_);
v___x_458_ = lean_box_uint32(v___x_457_);
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
v___x_460_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_455_, v___x_456_, v___x_459_);
v___x_461_ = lean_box(v___x_460_);
v_result_462_ = lean_array_push(v_result_454_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(2u);
v___x_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_451_);
lean_ctor_set(v___x_464_, 2, v___x_452_);
v___x_465_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_447_, v___x_464_, v_result_462_, v___x_463_);
lean_dec_ref_known(v___x_464_, 3);
v___x_466_ = lean_nat_sub(v___x_451_, v___x_463_);
v___x_467_ = lean_string_utf8_get(v_string_447_, v___x_466_);
lean_dec(v___x_466_);
v___x_468_ = lean_box_uint32(v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
v___x_470_ = lean_nat_sub(v___x_451_, v___x_452_);
v___x_471_ = lean_string_utf8_get(v_string_447_, v___x_470_);
lean_dec(v___x_470_);
v___x_472_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_469_, v___x_471_, v___x_455_);
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_array_push(v___x_465_, v___x_473_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; uint32_t v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_string_utf8_get(v_string_447_, v___x_449_);
v___x_477_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_475_, v___x_476_, v___x_475_);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_452_);
v___x_479_ = lean_box(v___x_477_);
v___x_480_ = lean_array_push(v___x_478_, v___x_479_);
return v___x_480_;
}
}
else
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0));
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* v_string_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_482_);
lean_dec_ref(v_string_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* v_s_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* v_s_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_486_);
lean_dec_ref(v_s_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* v_string_488_, lean_object* v_range_489_, lean_object* v_b_490_, lean_object* v_i_491_, lean_object* v_hs_492_, lean_object* v_hl_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_488_, v_range_489_, v_b_490_, v_i_491_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* v_string_495_, lean_object* v_range_496_, lean_object* v_b_497_, lean_object* v_i_498_, lean_object* v_hs_499_, lean_object* v_hl_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_495_, v_range_496_, v_b_497_, v_i_498_, v_hs_499_, v_hl_500_);
lean_dec(v_i_498_);
lean_dec_ref(v_range_496_);
lean_dec_ref(v_string_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* v_string_502_, lean_object* v_range_503_, lean_object* v_b_504_, lean_object* v_i_505_, lean_object* v_hs_506_, lean_object* v_hl_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_502_, v_range_503_, v_b_504_, v_i_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_string_509_, lean_object* v_range_510_, lean_object* v_b_511_, lean_object* v_i_512_, lean_object* v_hs_513_, lean_object* v_hl_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_509_, v_range_510_, v_b_511_, v_i_512_, v_hs_513_, v_hl_514_);
lean_dec_ref(v_range_510_);
lean_dec_ref(v_string_509_);
return v_res_515_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0(void){
_start:
{
lean_object* v___x_516_; uint16_t v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_int16_of_nat(v___x_516_);
return v___x_517_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default(void){
_start:
{
uint16_t v___x_518_; 
v___x_518_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_518_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore(void){
_start:
{
uint16_t v___x_519_; 
v___x_519_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
return v___x_519_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0(void){
_start:
{
lean_object* v___x_520_; uint16_t v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(32768u);
v___x_521_ = lean_int16_of_nat(v___x_520_);
return v___x_521_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1(void){
_start:
{
uint16_t v___x_522_; uint16_t v___x_523_; 
v___x_522_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0);
v___x_523_ = lean_int16_neg(v___x_522_);
return v___x_523_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful(void){
_start:
{
uint16_t v___x_524_; 
v___x_524_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
return v___x_524_;
}
}
uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t v_x_525_){
_start:
{
uint16_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_527_ = lean_int16_dec_le(v_x_525_, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_525_ = stack[0].m_num;
uint8_t v_res_528_;
v_res_528_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_525_);
stack->m_num = v_res_528_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* v_x_529_){
_start:
{
uint16_t v_x_boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_x_boxed_530_ = lean_unbox(v_x_529_);
v_res_531_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_530_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t v_x_533_, lean_object* v_f_534_){
_start:
{
uint16_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_536_ = lean_int16_dec_le(v_x_533_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; uint16_t v___x_539_; 
v___x_537_ = lean_box(v_x_533_);
v___x_538_ = lean_apply_1(v_f_534_, v___x_537_);
v___x_539_ = lean_unbox(v___x_538_);
return v___x_539_;
}
else
{
lean_dec_ref(v_f_534_);
return v_x_533_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_533_ = stack[0].m_num;
lean_object* v_f_534_ = stack[1].m_obj;
uint16_t v_res_540_;
v_res_540_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_533_, v_f_534_);
stack->m_num = v_res_540_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* v_x_541_, lean_object* v_f_542_){
_start:
{
uint16_t v_x_boxed_543_; uint16_t v_res_544_; lean_object* v_r_545_; 
v_x_boxed_543_ = lean_unbox(v_x_541_);
v_res_544_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_boxed_543_, v_f_542_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t v_x_546_){
_start:
{
uint16_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_548_ = lean_int16_dec_le(v_x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_box(v_x_546_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(0);
return v___x_551_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_546_ = stack[0].m_num;
lean_object* v_res_552_;
v_res_552_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_546_);
stack->m_obj
 = v_res_552_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* v_x_553_){
_start:
{
uint16_t v_x_boxed_554_; lean_object* v_res_555_; 
v_x_boxed_554_ = lean_unbox(v_x_553_);
v_res_555_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_boxed_554_);
return v_res_555_;
}
}
lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t v_x_556_){
_start:
{
uint16_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_558_ = lean_int16_dec_le(v_x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_int16_to_int(v_x_556_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_box(0);
return v___x_561_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_556_ = stack[0].m_num;
lean_object* v_res_562_;
v_res_562_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_556_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* v_x_563_){
_start:
{
uint16_t v_x_boxed_564_; lean_object* v_res_565_; 
v_x_boxed_564_ = lean_unbox(v_x_563_);
v_res_565_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_564_);
return v_res_565_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
v___x_570_ = lean_unsigned_to_nat(2u);
v___x_571_ = lean_unsigned_to_nat(127u);
v___x_572_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
v___x_573_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
v___x_574_ = l_mkPanicMessageWithDecl(v___x_573_, v___x_572_, v___x_571_, v___x_570_, v___x_569_);
return v___x_574_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t v_x_575_){
_start:
{
uint16_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_577_ = lean_int16_dec_eq(v_x_575_, v___x_576_);
if (v___x_577_ == 0)
{
return v_x_575_;
}
else
{
uint16_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint16_t v___x_582_; 
v___x_578_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_579_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_580_ = lean_box(v___x_578_);
v___x_581_ = l_panic___redArg(v___x_580_, v___x_579_);
lean_dec(v___x_580_);
v___x_582_ = lean_unbox(v___x_581_);
lean_dec(v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_575_ = stack[0].m_num;
uint16_t v_res_583_;
v_res_583_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_575_);
stack->m_num = v_res_583_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* v_x_584_){
_start:
{
uint16_t v_x_boxed_585_; uint16_t v_res_586_; lean_object* v_r_587_; 
v_x_boxed_585_ = lean_unbox(v_x_584_);
v_res_586_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_boxed_585_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t v_missScore_588_, uint16_t v_matchScore_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_int16_dec_le(v_missScore_588_, v_matchScore_589_);
if (v___x_590_ == 0)
{
return v_missScore_588_;
}
else
{
return v_matchScore_589_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest_0interp(lean_interpreter_value* stack)
{
uint16_t v_missScore_588_ = stack[0].m_num;
uint16_t v_matchScore_589_ = stack[1].m_num;
uint16_t v_res_591_;
v_res_591_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_588_, v_matchScore_589_);
stack->m_num = v_res_591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* v_missScore_592_, lean_object* v_matchScore_593_){
_start:
{
uint16_t v_missScore_boxed_594_; uint16_t v_matchScore_boxed_595_; uint16_t v_res_596_; lean_object* v_r_597_; 
v_missScore_boxed_594_ = lean_unbox(v_missScore_592_);
v_matchScore_boxed_595_ = lean_unbox(v_matchScore_593_);
v_res_596_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_boxed_594_, v_matchScore_boxed_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* v_word_598_, lean_object* v_patternIdx_599_, lean_object* v_wordIdx_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = lean_string_length(v_word_598_);
v___x_602_ = lean_nat_mul(v_patternIdx_599_, v___x_601_);
v___x_603_ = lean_unsigned_to_nat(2u);
v___x_604_ = lean_nat_mul(v___x_602_, v___x_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_nat_mul(v_wordIdx_600_, v___x_603_);
v___x_606_ = lean_nat_add(v___x_604_, v___x_605_);
lean_dec(v___x_605_);
lean_dec(v___x_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* v_word_607_, lean_object* v_patternIdx_608_, lean_object* v_wordIdx_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(v_word_607_, v_patternIdx_608_, v_wordIdx_609_);
lean_dec(v_wordIdx_609_);
lean_dec(v_patternIdx_608_);
lean_dec_ref(v_word_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* v_word_611_, lean_object* v_patternIdx_612_, lean_object* v_wordIdx_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_string_length(v_word_611_);
v___x_615_ = lean_nat_mul(v_patternIdx_612_, v___x_614_);
v___x_616_ = lean_nat_add(v___x_615_, v_wordIdx_613_);
lean_dec(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* v_word_617_, lean_object* v_patternIdx_618_, lean_object* v_wordIdx_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(v_word_617_, v_patternIdx_618_, v_wordIdx_619_);
lean_dec(v_wordIdx_619_);
lean_dec(v_patternIdx_618_);
lean_dec_ref(v_word_617_);
return v_res_620_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* v_word_621_, lean_object* v_result_622_, lean_object* v_patternIdx_623_, lean_object* v_wordIdx_624_){
_start:
{
uint16_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint16_t v___x_634_; 
v___x_625_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_626_ = lean_string_length(v_word_621_);
v___x_627_ = lean_nat_mul(v_patternIdx_623_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(2u);
v___x_629_ = lean_nat_mul(v___x_627_, v___x_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_nat_mul(v_wordIdx_624_, v___x_628_);
v___x_631_ = lean_nat_add(v___x_629_, v___x_630_);
lean_dec(v___x_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(v___x_625_);
v___x_633_ = lean_array_get(v___x_632_, v_result_622_, v___x_631_);
lean_dec(v___x_631_);
lean_dec(v___x_632_);
v___x_634_ = lean_unbox(v___x_633_);
lean_dec(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss_0interp(lean_interpreter_value* stack)
{
lean_object* v_word_621_ = stack[0].m_obj;
lean_object* v_result_622_ = stack[1].m_obj;
lean_object* v_patternIdx_623_ = stack[2].m_obj;
lean_object* v_wordIdx_624_ = stack[3].m_obj;
uint16_t v_res_635_;
v_res_635_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_621_, v_result_622_, v_patternIdx_623_, v_wordIdx_624_);
stack->m_num = v_res_635_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* v_word_636_, lean_object* v_result_637_, lean_object* v_patternIdx_638_, lean_object* v_wordIdx_639_){
_start:
{
uint16_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_636_, v_result_637_, v_patternIdx_638_, v_wordIdx_639_);
lean_dec(v_wordIdx_639_);
lean_dec(v_patternIdx_638_);
lean_dec_ref(v_result_637_);
lean_dec_ref(v_word_636_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* v_word_642_, lean_object* v_result_643_, lean_object* v_patternIdx_644_, lean_object* v_wordIdx_645_){
_start:
{
uint16_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint16_t v___x_657_; 
v___x_646_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_647_ = lean_string_length(v_word_642_);
v___x_648_ = lean_nat_mul(v_patternIdx_644_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(2u);
v___x_650_ = lean_nat_mul(v___x_648_, v___x_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_nat_mul(v_wordIdx_645_, v___x_649_);
v___x_652_ = lean_nat_add(v___x_650_, v___x_651_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(v___x_646_);
v___x_656_ = lean_array_get(v___x_655_, v_result_643_, v___x_654_);
lean_dec(v___x_654_);
lean_dec(v___x_655_);
v___x_657_ = lean_unbox(v___x_656_);
lean_dec(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_word_642_ = stack[0].m_obj;
lean_object* v_result_643_ = stack[1].m_obj;
lean_object* v_patternIdx_644_ = stack[2].m_obj;
lean_object* v_wordIdx_645_ = stack[3].m_obj;
uint16_t v_res_658_;
v_res_658_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_642_, v_result_643_, v_patternIdx_644_, v_wordIdx_645_);
stack->m_num = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* v_word_659_, lean_object* v_result_660_, lean_object* v_patternIdx_661_, lean_object* v_wordIdx_662_){
_start:
{
uint16_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_659_, v_result_660_, v_patternIdx_661_, v_wordIdx_662_);
lean_dec(v_wordIdx_662_);
lean_dec(v_patternIdx_661_);
lean_dec_ref(v_result_660_);
lean_dec_ref(v_word_659_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* v_word_665_, lean_object* v_result_666_, lean_object* v_patternIdx_667_, lean_object* v_wordIdx_668_, uint16_t v_missValue_669_, uint16_t v_matchValue_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_idx_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_671_ = lean_string_length(v_word_665_);
v___x_672_ = lean_nat_mul(v_patternIdx_667_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(2u);
v___x_674_ = lean_nat_mul(v___x_672_, v___x_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_nat_mul(v_wordIdx_668_, v___x_673_);
v_idx_676_ = lean_nat_add(v___x_674_, v___x_675_);
lean_dec(v___x_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(v_missValue_669_);
v___x_678_ = lean_array_set(v_result_666_, v_idx_676_, v___x_677_);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_idx_676_, v___x_679_);
lean_dec(v_idx_676_);
v___x_681_ = lean_box(v_matchValue_670_);
v___x_682_ = lean_array_set(v___x_678_, v___x_680_, v___x_681_);
lean_dec(v___x_680_);
return v___x_682_;
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_word_665_ = stack[0].m_obj;
lean_object* v_result_666_ = stack[1].m_obj;
lean_object* v_patternIdx_667_ = stack[2].m_obj;
lean_object* v_wordIdx_668_ = stack[3].m_obj;
uint16_t v_missValue_669_ = stack[4].m_num;
uint16_t v_matchValue_670_ = stack[5].m_num;
lean_object* v_res_683_;
v_res_683_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_665_, v_result_666_, v_patternIdx_667_, v_wordIdx_668_, v_missValue_669_, v_matchValue_670_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* v_word_684_, lean_object* v_result_685_, lean_object* v_patternIdx_686_, lean_object* v_wordIdx_687_, lean_object* v_missValue_688_, lean_object* v_matchValue_689_){
_start:
{
uint16_t v_missValue_boxed_690_; uint16_t v_matchValue_boxed_691_; lean_object* v_res_692_; 
v_missValue_boxed_690_ = lean_unbox(v_missValue_688_);
v_matchValue_boxed_691_ = lean_unbox(v_matchValue_689_);
v_res_692_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_684_, v_result_685_, v_patternIdx_686_, v_wordIdx_687_, v_missValue_boxed_690_, v_matchValue_boxed_691_);
lean_dec(v_wordIdx_687_);
lean_dec(v_patternIdx_686_);
lean_dec_ref(v_word_684_);
return v_res_692_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0(void){
_start:
{
lean_object* v___x_693_; uint16_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_int16_of_nat(v___x_693_);
return v___x_694_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1(void){
_start:
{
lean_object* v___x_695_; uint16_t v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(3u);
v___x_696_ = lean_int16_of_nat(v___x_695_);
return v___x_696_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t v_wordRole_697_, uint8_t v_wordStart_698_){
_start:
{
if (v_wordStart_698_ == 0)
{
if (v_wordRole_697_ == 0)
{
uint16_t v___x_699_; 
v___x_699_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
return v___x_699_;
}
else
{
uint16_t v___x_700_; 
v___x_700_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_700_;
}
}
else
{
uint16_t v___x_701_; 
v___x_701_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
return v___x_701_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty_0interp(lean_interpreter_value* stack)
{
uint8_t v_wordRole_697_ = stack[0].m_num;
uint8_t v_wordStart_698_ = stack[1].m_num;
uint16_t v_res_702_;
v_res_702_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_697_, v_wordStart_698_);
stack->m_num = v_res_702_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* v_wordRole_703_, lean_object* v_wordStart_704_){
_start:
{
uint8_t v_wordRole_boxed_705_; uint8_t v_wordStart_boxed_706_; uint16_t v_res_707_; lean_object* v_r_708_; 
v_wordRole_boxed_705_ = lean_unbox(v_wordRole_703_);
v_wordStart_boxed_706_ = lean_unbox(v_wordStart_704_);
v_res_707_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_boxed_705_, v_wordStart_boxed_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t v_patternChar_709_, uint32_t v_wordChar_710_, uint8_t v_patternRole_711_, uint8_t v_wordRole_712_){
_start:
{
uint32_t v___y_714_; uint32_t v___y_715_; uint32_t v___y_719_; uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 65;
v___x_727_ = lean_uint32_dec_le(v___x_726_, v_patternChar_709_);
if (v___x_727_ == 0)
{
v___y_719_ = v_patternChar_709_;
goto v___jp_718_;
}
else
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 90;
v___x_729_ = lean_uint32_dec_le(v_patternChar_709_, v___x_728_);
if (v___x_729_ == 0)
{
v___y_719_ = v_patternChar_709_;
goto v___jp_718_;
}
else
{
uint32_t v___x_730_; uint32_t v___x_731_; 
v___x_730_ = 32;
v___x_731_ = lean_uint32_add(v_patternChar_709_, v___x_730_);
v___y_719_ = v___x_731_;
goto v___jp_718_;
}
}
v___jp_713_:
{
uint8_t v___x_716_; 
v___x_716_ = lean_uint32_dec_eq(v___y_714_, v___y_715_);
if (v___x_716_ == 0)
{
return v___x_716_;
}
else
{
if (v_patternRole_711_ == 0)
{
if (v_wordRole_712_ == 0)
{
return v___x_716_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
else
{
return v___x_716_;
}
}
}
v___jp_718_:
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 65;
v___x_721_ = lean_uint32_dec_le(v___x_720_, v_wordChar_710_);
if (v___x_721_ == 0)
{
v___y_714_ = v___y_719_;
v___y_715_ = v_wordChar_710_;
goto v___jp_713_;
}
else
{
uint32_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 90;
v___x_723_ = lean_uint32_dec_le(v_wordChar_710_, v___x_722_);
if (v___x_723_ == 0)
{
v___y_714_ = v___y_719_;
v___y_715_ = v_wordChar_710_;
goto v___jp_713_;
}
else
{
uint32_t v___x_724_; uint32_t v___x_725_; 
v___x_724_ = 32;
v___x_725_ = lean_uint32_add(v_wordChar_710_, v___x_724_);
v___y_714_ = v___y_719_;
v___y_715_ = v___x_725_;
goto v___jp_713_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch_0interp(lean_interpreter_value* stack)
{
uint32_t v_patternChar_709_ = stack[0].m_num;
uint32_t v_wordChar_710_ = stack[1].m_num;
uint8_t v_patternRole_711_ = stack[2].m_num;
uint8_t v_wordRole_712_ = stack[3].m_num;
uint8_t v_res_732_;
v_res_732_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v_patternChar_709_, v_wordChar_710_, v_patternRole_711_, v_wordRole_712_);
stack->m_num = v_res_732_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object* v_patternChar_733_, lean_object* v_wordChar_734_, lean_object* v_patternRole_735_, lean_object* v_wordRole_736_){
_start:
{
uint32_t v_patternChar_boxed_737_; uint32_t v_wordChar_boxed_738_; uint8_t v_patternRole_boxed_739_; uint8_t v_wordRole_boxed_740_; uint8_t v_res_741_; lean_object* v_r_742_; 
v_patternChar_boxed_737_ = lean_unbox_uint32(v_patternChar_733_);
lean_dec(v_patternChar_733_);
v_wordChar_boxed_738_ = lean_unbox_uint32(v_wordChar_734_);
lean_dec(v_wordChar_734_);
v_patternRole_boxed_739_ = lean_unbox(v_patternRole_735_);
v_wordRole_boxed_740_ = lean_unbox(v_wordRole_736_);
v_res_741_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v_patternChar_boxed_737_, v_wordChar_boxed_738_, v_patternRole_boxed_739_, v_wordRole_boxed_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0(void){
_start:
{
lean_object* v___x_743_; uint16_t v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(2u);
v___x_744_ = lean_int16_of_nat(v___x_743_);
return v___x_744_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1(void){
_start:
{
uint16_t v_score_745_; uint16_t v_score_746_; 
v_score_745_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v_score_746_ = lean_int16_add(v_score_745_, v_score_745_);
return v_score_746_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object* v_pattern_747_, lean_object* v_word_748_, lean_object* v_patternIdx_749_, lean_object* v_wordIdx_750_, uint8_t v_patternRole_751_, uint8_t v_wordRole_752_, uint16_t v_consecutive_753_){
_start:
{
uint16_t v_score_755_; uint16_t v_score_760_; lean_object* v___x_765_; uint16_t v_score_767_; uint16_t v_score_776_; uint32_t v___x_779_; uint32_t v___x_780_; uint8_t v___x_781_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v_score_776_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_779_ = lean_string_utf8_get(v_pattern_747_, v_patternIdx_749_);
v___x_780_ = lean_string_utf8_get(v_word_748_, v_wordIdx_750_);
v___x_781_ = lean_uint32_dec_eq(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
if (v_patternRole_751_ == 0)
{
if (v_wordRole_752_ == 0)
{
goto v___jp_777_;
}
else
{
v_score_767_ = v_score_776_;
goto v___jp_766_;
}
}
else
{
v_score_767_ = v_score_776_;
goto v___jp_766_;
}
}
else
{
goto v___jp_777_;
}
v___jp_754_:
{
uint16_t v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_757_ = lean_int16_dec_le(v_consecutive_753_, v___x_756_);
if (v___x_757_ == 0)
{
uint16_t v_score_758_; 
v_score_758_ = lean_int16_add(v_score_755_, v_consecutive_753_);
return v_score_758_;
}
else
{
return v_score_755_;
}
}
v___jp_759_:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_nat_dec_eq(v_wordIdx_750_, v___x_761_);
if (v___x_762_ == 0)
{
v_score_755_ = v_score_760_;
goto v___jp_754_;
}
else
{
uint16_t v___x_763_; uint16_t v_score_764_; 
v___x_763_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
v_score_764_ = lean_int16_add(v_score_760_, v___x_763_);
v_score_755_ = v_score_764_;
goto v___jp_754_;
}
}
v___jp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_string_length(v_word_748_);
v___x_769_ = lean_nat_sub(v___x_768_, v___x_765_);
v___x_770_ = lean_nat_dec_eq(v_wordIdx_750_, v___x_769_);
lean_dec(v___x_769_);
if (v___x_770_ == 0)
{
v_score_760_ = v_score_767_;
goto v___jp_759_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_string_length(v_pattern_747_);
v___x_772_ = lean_nat_sub(v___x_771_, v___x_765_);
v___x_773_ = lean_nat_dec_eq(v_patternIdx_749_, v___x_772_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
v_score_760_ = v_score_767_;
goto v___jp_759_;
}
else
{
uint16_t v___x_774_; uint16_t v_score_775_; 
v___x_774_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
v_score_775_ = lean_int16_add(v_score_767_, v___x_774_);
v_score_760_ = v_score_775_;
goto v___jp_759_;
}
}
}
v___jp_777_:
{
uint16_t v_score_778_; 
v_score_778_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
v_score_767_ = v_score_778_;
goto v___jp_766_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_747_ = stack[0].m_obj;
lean_object* v_word_748_ = stack[1].m_obj;
lean_object* v_patternIdx_749_ = stack[2].m_obj;
lean_object* v_wordIdx_750_ = stack[3].m_obj;
uint8_t v_patternRole_751_ = stack[4].m_num;
uint8_t v_wordRole_752_ = stack[5].m_num;
uint16_t v_consecutive_753_ = stack[6].m_num;
uint16_t v_res_782_;
v_res_782_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_747_, v_word_748_, v_patternIdx_749_, v_wordIdx_750_, v_patternRole_751_, v_wordRole_752_, v_consecutive_753_);
stack->m_num = v_res_782_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* v_pattern_783_, lean_object* v_word_784_, lean_object* v_patternIdx_785_, lean_object* v_wordIdx_786_, lean_object* v_patternRole_787_, lean_object* v_wordRole_788_, lean_object* v_consecutive_789_){
_start:
{
uint8_t v_patternRole_boxed_790_; uint8_t v_wordRole_boxed_791_; uint16_t v_consecutive_boxed_792_; uint16_t v_res_793_; lean_object* v_r_794_; 
v_patternRole_boxed_790_ = lean_unbox(v_patternRole_787_);
v_wordRole_boxed_791_ = lean_unbox(v_wordRole_788_);
v_consecutive_boxed_792_ = lean_unbox(v_consecutive_789_);
v_res_793_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_783_, v_word_784_, v_patternIdx_785_, v_wordIdx_786_, v_patternRole_boxed_790_, v_wordRole_boxed_791_, v_consecutive_boxed_792_);
lean_dec(v_wordIdx_786_);
lean_dec(v_patternIdx_785_);
lean_dec_ref(v_word_784_);
lean_dec_ref(v_pattern_783_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* v_msg_795_){
_start:
{
uint16_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint16_t v___x_799_; 
v___x_796_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_797_ = lean_box(v___x_796_);
v___x_798_ = lean_panic_fn_borrowed(v___x_797_, v_msg_795_);
lean_dec(v___x_797_);
v___x_799_ = lean_unbox(v___x_798_);
lean_dec(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_795_ = stack[0].m_obj;
uint16_t v_res_800_;
v_res_800_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_795_);
stack->m_num = v_res_800_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* v_msg_801_){
_start:
{
uint16_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_801_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* v___x_804_, lean_object* v_a_805_, uint16_t v_x_806_){
_start:
{
uint16_t v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_808_ = lean_int16_dec_le(v_x_806_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_le(v___x_804_, v_a_805_);
if (v___x_809_ == 0)
{
return v_x_806_;
}
else
{
uint16_t v___x_810_; uint16_t v___x_811_; 
v___x_810_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_811_ = lean_int16_add(v_x_806_, v___x_810_);
return v___x_811_;
}
}
else
{
return v_x_806_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_804_ = stack[0].m_obj;
lean_object* v_a_805_ = stack[1].m_obj;
uint16_t v_x_806_ = stack[2].m_num;
uint16_t v_res_812_;
v_res_812_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_804_, v_a_805_, v_x_806_);
stack->m_num = v_res_812_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* v___x_813_, lean_object* v_a_814_, lean_object* v_x_815_){
_start:
{
uint16_t v_x_boxed_816_; uint16_t v_res_817_; lean_object* v_r_818_; 
v_x_boxed_816_ = lean_unbox(v_x_815_);
v_res_817_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_813_, v_a_814_, v_x_boxed_816_);
lean_dec(v_a_814_);
lean_dec(v___x_813_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* v_pattern_819_, lean_object* v_word_820_, lean_object* v_a_821_, lean_object* v_a_822_, uint8_t v___x_823_, uint8_t v___x_824_, lean_object* v___x_825_, uint16_t v_x_826_){
_start:
{
uint16_t v_matchScore_827_; uint8_t v___x_828_; 
v_matchScore_827_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_828_ = lean_int16_dec_le(v_x_826_, v_matchScore_827_);
if (v___x_828_ == 0)
{
uint16_t v___x_829_; uint16_t v___x_830_; uint16_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint16_t v___x_834_; uint16_t v___x_835_; 
v___x_829_ = l_instInhabitedInt16;
v___x_830_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_819_, v_word_820_, v_a_821_, v_a_822_, v___x_823_, v___x_824_, v_matchScore_827_);
v___x_831_ = lean_int16_add(v_x_826_, v___x_830_);
v___x_832_ = lean_box(v___x_829_);
v___x_833_ = lean_array_get(v___x_832_, v___x_825_, v_a_822_);
lean_dec(v___x_832_);
v___x_834_ = lean_unbox(v___x_833_);
lean_dec(v___x_833_);
v___x_835_ = lean_int16_sub(v___x_831_, v___x_834_);
return v___x_835_;
}
else
{
return v_x_826_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_819_ = stack[0].m_obj;
lean_object* v_word_820_ = stack[1].m_obj;
lean_object* v_a_821_ = stack[2].m_obj;
lean_object* v_a_822_ = stack[3].m_obj;
uint8_t v___x_823_ = stack[4].m_num;
uint8_t v___x_824_ = stack[5].m_num;
lean_object* v___x_825_ = stack[6].m_obj;
uint16_t v_x_826_ = stack[7].m_num;
uint16_t v_res_836_;
v_res_836_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_819_, v_word_820_, v_a_821_, v_a_822_, v___x_823_, v___x_824_, v___x_825_, v_x_826_);
stack->m_num = v_res_836_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* v_pattern_837_, lean_object* v_word_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v___x_841_, lean_object* v___x_842_, lean_object* v___x_843_, lean_object* v_x_844_){
_start:
{
uint8_t v___x_3033__boxed_845_; uint8_t v___x_3034__boxed_846_; uint16_t v_x_boxed_847_; uint16_t v_res_848_; lean_object* v_r_849_; 
v___x_3033__boxed_845_ = lean_unbox(v___x_841_);
v___x_3034__boxed_846_ = lean_unbox(v___x_842_);
v_x_boxed_847_ = lean_unbox(v_x_844_);
v_res_848_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_837_, v_word_838_, v_a_839_, v_a_840_, v___x_3033__boxed_845_, v___x_3034__boxed_846_, v___x_843_, v_x_boxed_847_);
lean_dec_ref(v___x_843_);
lean_dec(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_word_838_);
lean_dec_ref(v_pattern_837_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* v_pattern_850_, lean_object* v_word_851_, lean_object* v_a_852_, lean_object* v_a_853_, uint8_t v___x_854_, uint8_t v___x_855_, uint16_t v___x_856_, uint16_t v_x_857_){
_start:
{
uint16_t v___y_859_; uint16_t v___x_862_; uint8_t v___x_863_; 
v___x_862_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_863_ = lean_int16_dec_le(v_x_857_, v___x_862_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
v___x_864_ = lean_int16_dec_eq(v___x_856_, v___x_862_);
if (v___x_864_ == 0)
{
v___y_859_ = v___x_856_;
goto v___jp_858_;
}
else
{
lean_object* v___x_865_; uint16_t v___x_866_; 
v___x_865_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_866_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_865_);
v___y_859_ = v___x_866_;
goto v___jp_858_;
}
}
else
{
return v_x_857_;
}
v___jp_858_:
{
uint16_t v___x_860_; uint16_t v___x_861_; 
v___x_860_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_850_, v_word_851_, v_a_852_, v_a_853_, v___x_854_, v___x_855_, v___y_859_);
v___x_861_ = lean_int16_add(v_x_857_, v___x_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_850_ = stack[0].m_obj;
lean_object* v_word_851_ = stack[1].m_obj;
lean_object* v_a_852_ = stack[2].m_obj;
lean_object* v_a_853_ = stack[3].m_obj;
uint8_t v___x_854_ = stack[4].m_num;
uint8_t v___x_855_ = stack[5].m_num;
uint16_t v___x_856_ = stack[6].m_num;
uint16_t v_x_857_ = stack[7].m_num;
uint16_t v_res_867_;
v_res_867_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_850_, v_word_851_, v_a_852_, v_a_853_, v___x_854_, v___x_855_, v___x_856_, v_x_857_);
stack->m_num = v_res_867_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* v_pattern_868_, lean_object* v_word_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_x_875_){
_start:
{
uint8_t v___x_3087__boxed_876_; uint8_t v___x_3088__boxed_877_; uint16_t v___x_3089__boxed_878_; uint16_t v_x_boxed_879_; uint16_t v_res_880_; lean_object* v_r_881_; 
v___x_3087__boxed_876_ = lean_unbox(v___x_872_);
v___x_3088__boxed_877_ = lean_unbox(v___x_873_);
v___x_3089__boxed_878_ = lean_unbox(v___x_874_);
v_x_boxed_879_ = lean_unbox(v_x_875_);
v_res_880_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_868_, v_word_869_, v_a_870_, v_a_871_, v___x_3087__boxed_876_, v___x_3088__boxed_877_, v___x_3089__boxed_878_, v_x_boxed_879_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_word_869_);
lean_dec_ref(v_pattern_868_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* v_word_882_, lean_object* v_a_883_, lean_object* v_pattern_884_, lean_object* v_patternRoles_885_, lean_object* v_wordRoles_886_, lean_object* v___x_887_, lean_object* v___x_888_, lean_object* v_range_889_, lean_object* v_b_890_, lean_object* v_i_891_){
_start:
{
lean_object* v_stop_892_; lean_object* v_step_893_; uint8_t v___x_894_; 
v_stop_892_ = lean_ctor_get(v_range_889_, 1);
v_step_893_ = lean_ctor_get(v_range_889_, 2);
v___x_894_ = lean_nat_dec_lt(v_i_891_, v_stop_892_);
if (v___x_894_ == 0)
{
lean_dec(v_i_891_);
return v_b_890_;
}
else
{
lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_1009_; 
v_fst_895_ = lean_ctor_get(v_b_890_, 0);
v_snd_896_ = lean_ctor_get(v_b_890_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_b_890_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_898_ = v_b_890_;
v_isShared_899_ = v_isSharedCheck_1009_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_inc(v_fst_895_);
lean_dec(v_b_890_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_1009_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
uint8_t v___x_900_; uint16_t v_matchScore_901_; uint16_t v___x_902_; lean_object* v___x_903_; uint16_t v___y_905_; lean_object* v_runLengths_906_; uint16_t v_matchScore_907_; uint16_t v___y_925_; lean_object* v___y_926_; uint16_t v___y_927_; uint16_t v___y_930_; uint8_t v___x_990_; 
v___x_900_ = 0;
v_matchScore_901_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_902_ = l_instInhabitedInt16;
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_dec_le(v___x_903_, v_i_891_);
if (v___x_990_ == 0)
{
v___y_930_ = v_matchScore_901_;
goto v___jp_929_;
}
else
{
lean_object* v___x_991_; uint16_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint16_t v___x_1004_; uint16_t v___x_1005_; uint8_t v___x_1006_; 
v___x_991_ = lean_nat_sub(v_i_891_, v___x_903_);
v___x_992_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_993_ = lean_string_length(v_word_882_);
v___x_994_ = lean_nat_mul(v_a_883_, v___x_993_);
v___x_995_ = lean_unsigned_to_nat(2u);
v___x_996_ = lean_nat_mul(v___x_994_, v___x_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_nat_mul(v___x_991_, v___x_995_);
lean_dec(v___x_991_);
v___x_998_ = lean_nat_add(v___x_996_, v___x_997_);
lean_dec(v___x_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(v___x_992_);
v___x_1000_ = lean_array_get(v___x_999_, v_fst_895_, v___x_998_);
lean_dec(v___x_999_);
v___x_1001_ = lean_nat_add(v___x_998_, v___x_903_);
lean_dec(v___x_998_);
v___x_1002_ = lean_box(v___x_992_);
v___x_1003_ = lean_array_get(v___x_1002_, v_fst_895_, v___x_1001_);
lean_dec(v___x_1001_);
lean_dec(v___x_1002_);
v___x_1004_ = lean_unbox(v___x_1000_);
v___x_1005_ = lean_unbox(v___x_1003_);
v___x_1006_ = lean_int16_dec_le(v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
uint16_t v___x_1007_; 
lean_dec(v___x_1003_);
v___x_1007_ = lean_unbox(v___x_1000_);
lean_dec(v___x_1000_);
v___y_930_ = v___x_1007_;
goto v___jp_929_;
}
else
{
uint16_t v___x_1008_; 
lean_dec(v___x_1000_);
v___x_1008_ = lean_unbox(v___x_1003_);
lean_dec(v___x_1003_);
v___y_930_ = v___x_1008_;
goto v___jp_929_;
}
}
v___jp_904_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_idx_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_908_ = lean_string_length(v_word_882_);
v___x_909_ = lean_nat_mul(v_a_883_, v___x_908_);
v___x_910_ = lean_unsigned_to_nat(2u);
v___x_911_ = lean_nat_mul(v___x_909_, v___x_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_nat_mul(v_i_891_, v___x_910_);
v_idx_913_ = lean_nat_add(v___x_911_, v___x_912_);
lean_dec(v___x_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(v___y_905_);
v___x_915_ = lean_array_set(v_fst_895_, v_idx_913_, v___x_914_);
v___x_916_ = lean_nat_add(v_idx_913_, v___x_903_);
lean_dec(v_idx_913_);
v___x_917_ = lean_box(v_matchScore_907_);
v___x_918_ = lean_array_set(v___x_915_, v___x_916_, v___x_917_);
lean_dec(v___x_916_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_runLengths_906_);
lean_ctor_set(v___x_898_, 0, v___x_918_);
v___x_920_ = v___x_898_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_runLengths_906_);
v___x_920_ = v_reuseFailAlloc_923_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_nat_add(v_i_891_, v_step_893_);
lean_dec(v_i_891_);
v_b_890_ = v___x_920_;
v_i_891_ = v___x_921_;
goto _start;
}
}
v___jp_924_:
{
uint16_t v___x_928_; 
v___x_928_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_888_, v_i_891_, v___y_927_);
v___y_905_ = v___y_925_;
v_runLengths_906_ = v___y_926_;
v_matchScore_907_ = v___x_928_;
goto v___jp_904_;
}
v___jp_929_:
{
uint32_t v___x_931_; uint32_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; uint8_t v___x_938_; uint8_t v___x_939_; 
v___x_931_ = lean_string_utf8_get(v_pattern_884_, v_a_883_);
v___x_932_ = lean_string_utf8_get(v_word_882_, v_i_891_);
v___x_933_ = lean_box(v___x_900_);
v___x_934_ = lean_array_get(v___x_933_, v_patternRoles_885_, v_a_883_);
lean_dec(v___x_933_);
v___x_935_ = lean_box(v___x_900_);
v___x_936_ = lean_array_get(v___x_935_, v_wordRoles_886_, v_i_891_);
lean_dec(v___x_935_);
v___x_937_ = lean_unbox(v___x_934_);
v___x_938_ = lean_unbox(v___x_936_);
v___x_939_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_931_, v___x_932_, v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec(v___x_936_);
lean_dec(v___x_934_);
v___y_905_ = v___y_930_;
v_runLengths_906_ = v_snd_896_;
v_matchScore_907_ = v_matchScore_901_;
goto v___jp_904_;
}
else
{
uint8_t v___x_940_; 
v___x_940_ = lean_nat_dec_le(v___x_903_, v_a_883_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint16_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint16_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint16_t v___x_952_; uint16_t v___x_953_; uint8_t v___x_954_; 
v___x_941_ = lean_string_length(v_word_882_);
v___x_942_ = lean_nat_mul(v_a_883_, v___x_941_);
v___x_943_ = lean_nat_add(v___x_942_, v_i_891_);
lean_dec(v___x_942_);
v___x_944_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_945_ = lean_box(v___x_944_);
v___x_946_ = lean_array_set(v_snd_896_, v___x_943_, v___x_945_);
lean_dec(v___x_943_);
v___x_947_ = lean_unbox(v___x_934_);
lean_dec(v___x_934_);
v___x_948_ = lean_unbox(v___x_936_);
lean_dec(v___x_936_);
v___x_949_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_884_, v_word_882_, v_a_883_, v_i_891_, v___x_947_, v___x_948_, v_matchScore_901_);
v___x_950_ = lean_box(v___x_902_);
v___x_951_ = lean_array_get(v___x_950_, v___x_887_, v_i_891_);
lean_dec(v___x_950_);
v___x_952_ = lean_unbox(v___x_951_);
lean_dec(v___x_951_);
v___x_953_ = lean_int16_sub(v___x_949_, v___x_952_);
v___x_954_ = lean_int16_dec_eq(v___x_953_, v_matchScore_901_);
if (v___x_954_ == 0)
{
v___y_905_ = v___y_930_;
v_runLengths_906_ = v___x_946_;
v_matchScore_907_ = v___x_953_;
goto v___jp_904_;
}
else
{
lean_object* v___x_955_; uint16_t v___x_956_; 
v___x_955_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_956_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_955_);
v___y_905_ = v___y_930_;
v_runLengths_906_ = v___x_946_;
v_matchScore_907_ = v___x_956_;
goto v___jp_904_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint16_t v___x_964_; uint16_t v___x_965_; uint16_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint16_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; uint8_t v___x_979_; uint16_t v___x_980_; uint16_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; uint8_t v___x_986_; uint16_t v___x_987_; uint16_t v___x_988_; uint8_t v___x_989_; 
v___x_957_ = lean_nat_sub(v_a_883_, v___x_903_);
v___x_958_ = lean_nat_sub(v_i_891_, v___x_903_);
v___x_959_ = lean_string_length(v_word_882_);
v___x_960_ = lean_nat_mul(v___x_957_, v___x_959_);
lean_dec(v___x_957_);
v___x_961_ = lean_nat_add(v___x_960_, v___x_958_);
v___x_962_ = lean_box(v___x_902_);
v___x_963_ = lean_array_get(v___x_962_, v_snd_896_, v___x_961_);
lean_dec(v___x_961_);
lean_dec(v___x_962_);
v___x_964_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_965_ = lean_unbox(v___x_963_);
lean_dec(v___x_963_);
v___x_966_ = lean_int16_add(v___x_965_, v___x_964_);
v___x_967_ = lean_nat_mul(v_a_883_, v___x_959_);
v___x_968_ = lean_nat_add(v___x_967_, v_i_891_);
lean_dec(v___x_967_);
v___x_969_ = lean_box(v___x_966_);
v___x_970_ = lean_array_set(v_snd_896_, v___x_968_, v___x_969_);
lean_dec(v___x_968_);
v___x_971_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = lean_nat_mul(v___x_960_, v___x_972_);
lean_dec(v___x_960_);
v___x_974_ = lean_nat_mul(v___x_958_, v___x_972_);
lean_dec(v___x_958_);
v___x_975_ = lean_nat_add(v___x_973_, v___x_974_);
lean_dec(v___x_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(v___x_971_);
v___x_977_ = lean_array_get(v___x_976_, v_fst_895_, v___x_975_);
lean_dec(v___x_976_);
v___x_978_ = lean_unbox(v___x_934_);
v___x_979_ = lean_unbox(v___x_936_);
v___x_980_ = lean_unbox(v___x_977_);
lean_dec(v___x_977_);
v___x_981_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_884_, v_word_882_, v_a_883_, v_i_891_, v___x_978_, v___x_979_, v___x_887_, v___x_980_);
v___x_982_ = lean_nat_add(v___x_975_, v___x_903_);
lean_dec(v___x_975_);
v___x_983_ = lean_box(v___x_971_);
v___x_984_ = lean_array_get(v___x_983_, v_fst_895_, v___x_982_);
lean_dec(v___x_982_);
lean_dec(v___x_983_);
v___x_985_ = lean_unbox(v___x_934_);
lean_dec(v___x_934_);
v___x_986_ = lean_unbox(v___x_936_);
lean_dec(v___x_936_);
v___x_987_ = lean_unbox(v___x_984_);
lean_dec(v___x_984_);
v___x_988_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_884_, v_word_882_, v_a_883_, v_i_891_, v___x_985_, v___x_986_, v___x_966_, v___x_987_);
v___x_989_ = lean_int16_dec_le(v___x_981_, v___x_988_);
if (v___x_989_ == 0)
{
v___y_925_ = v___y_930_;
v___y_926_ = v___x_970_;
v___y_927_ = v___x_981_;
goto v___jp_924_;
}
else
{
v___y_925_ = v___y_930_;
v___y_926_ = v___x_970_;
v___y_927_ = v___x_988_;
goto v___jp_924_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* v_word_1010_, lean_object* v_a_1011_, lean_object* v_pattern_1012_, lean_object* v_patternRoles_1013_, lean_object* v_wordRoles_1014_, lean_object* v___x_1015_, lean_object* v___x_1016_, lean_object* v_range_1017_, lean_object* v_b_1018_, lean_object* v_i_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1010_, v_a_1011_, v_pattern_1012_, v_patternRoles_1013_, v_wordRoles_1014_, v___x_1015_, v___x_1016_, v_range_1017_, v_b_1018_, v_i_1019_);
lean_dec_ref(v_range_1017_);
lean_dec(v___x_1016_);
lean_dec_ref(v___x_1015_);
lean_dec_ref(v_wordRoles_1014_);
lean_dec_ref(v_patternRoles_1013_);
lean_dec_ref(v_pattern_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_word_1010_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object* v___x_1021_, lean_object* v___x_1022_, lean_object* v_word_1023_, lean_object* v_pattern_1024_, lean_object* v_patternRoles_1025_, lean_object* v_wordRoles_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_range_1029_, lean_object* v_b_1030_, lean_object* v_i_1031_){
_start:
{
lean_object* v_stop_1032_; lean_object* v_step_1033_; uint8_t v___x_1034_; 
v_stop_1032_ = lean_ctor_get(v_range_1029_, 1);
v_step_1033_ = lean_ctor_get(v_range_1029_, 2);
v___x_1034_ = lean_nat_dec_lt(v_i_1031_, v_stop_1032_);
if (v___x_1034_ == 0)
{
lean_dec(v_i_1031_);
return v_b_1030_;
}
else
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1060_; 
v_fst_1035_ = lean_ctor_get(v_b_1030_, 0);
v_snd_1036_ = lean_ctor_get(v_b_1030_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_b_1030_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1038_ = v_b_1030_;
v_isShared_1039_ = v_isSharedCheck_1060_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v_b_1030_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1060_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_sub(v___x_1021_, v_i_1031_);
v___x_1042_ = lean_nat_sub(v___x_1041_, v___x_1040_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_nat_sub(v___x_1022_, v___x_1042_);
lean_dec(v___x_1042_);
lean_inc(v_i_1031_);
v___x_1044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1044_, 0, v_i_1031_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
lean_ctor_set(v___x_1044_, 2, v___x_1040_);
if (v_isShared_1039_ == 0)
{
v___x_1046_ = v___x_1038_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_fst_1035_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1036_);
v___x_1046_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
lean_inc(v_i_1031_);
v___x_1047_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1023_, v_i_1031_, v_pattern_1024_, v_patternRoles_1025_, v_wordRoles_1026_, v___x_1027_, v___x_1028_, v___x_1044_, v___x_1046_, v_i_1031_);
lean_dec_ref_known(v___x_1044_, 3);
v_fst_1048_ = lean_ctor_get(v___x_1047_, 0);
v_snd_1049_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_inc(v_fst_1048_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_fst_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_snd_1049_);
v___x_1054_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_nat_add(v_i_1031_, v_step_1033_);
lean_dec(v_i_1031_);
v_b_1030_ = v___x_1054_;
v_i_1031_ = v___x_1055_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v_word_1063_, lean_object* v_pattern_1064_, lean_object* v_patternRoles_1065_, lean_object* v_wordRoles_1066_, lean_object* v___x_1067_, lean_object* v___x_1068_, lean_object* v_range_1069_, lean_object* v_b_1070_, lean_object* v_i_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1061_, v___x_1062_, v_word_1063_, v_pattern_1064_, v_patternRoles_1065_, v_wordRoles_1066_, v___x_1067_, v___x_1068_, v_range_1069_, v_b_1070_, v_i_1071_);
lean_dec_ref(v_range_1069_);
lean_dec(v___x_1068_);
lean_dec_ref(v___x_1067_);
lean_dec_ref(v_wordRoles_1066_);
lean_dec_ref(v_patternRoles_1065_);
lean_dec_ref(v_pattern_1064_);
lean_dec_ref(v_word_1063_);
lean_dec(v___x_1062_);
lean_dec(v___x_1061_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* v_word_1073_, lean_object* v_pattern_1074_, lean_object* v_patternRoles_1075_, lean_object* v_wordRoles_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v_range_1081_, lean_object* v_b_1082_, lean_object* v_i_1083_){
_start:
{
lean_object* v_stop_1084_; lean_object* v_step_1085_; uint8_t v___x_1086_; 
v_stop_1084_ = lean_ctor_get(v_range_1081_, 1);
v_step_1085_ = lean_ctor_get(v_range_1081_, 2);
v___x_1086_ = lean_nat_dec_lt(v_i_1083_, v_stop_1084_);
if (v___x_1086_ == 0)
{
lean_dec(v_i_1083_);
return v_b_1082_;
}
else
{
lean_object* v_fst_1087_; lean_object* v_snd_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1112_; 
v_fst_1087_ = lean_ctor_get(v_b_1082_, 0);
v_snd_1088_ = lean_ctor_get(v_b_1082_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_b_1082_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1090_ = v_b_1082_;
v_isShared_1091_ = v_isSharedCheck_1112_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_snd_1088_);
lean_inc(v_fst_1087_);
lean_dec(v_b_1082_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1112_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_sub(v___x_1079_, v_i_1083_);
v___x_1094_ = lean_nat_sub(v___x_1093_, v___x_1092_);
lean_dec(v___x_1093_);
v___x_1095_ = lean_nat_sub(v___x_1080_, v___x_1094_);
lean_dec(v___x_1094_);
lean_inc(v_i_1083_);
v___x_1096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1096_, 0, v_i_1083_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_ctor_set(v___x_1096_, 2, v___x_1092_);
if (v_isShared_1091_ == 0)
{
v___x_1098_ = v___x_1090_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1087_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_snd_1088_);
v___x_1098_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
lean_inc(v_i_1083_);
v___x_1099_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1073_, v_i_1083_, v_pattern_1074_, v_patternRoles_1075_, v_wordRoles_1076_, v___x_1077_, v___x_1078_, v___x_1096_, v___x_1098_, v_i_1083_);
lean_dec_ref_known(v___x_1096_, 3);
v_fst_1100_ = lean_ctor_get(v___x_1099_, 0);
v_snd_1101_ = lean_ctor_get(v___x_1099_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v___x_1099_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_snd_1101_);
lean_inc(v_fst_1100_);
lean_dec(v___x_1099_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_fst_1100_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_snd_1101_);
v___x_1106_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_nat_add(v_i_1083_, v_step_1085_);
lean_dec(v_i_1083_);
v___x_1108_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1079_, v___x_1080_, v_word_1073_, v_pattern_1074_, v_patternRoles_1075_, v_wordRoles_1076_, v___x_1077_, v___x_1078_, v_range_1081_, v___x_1106_, v___x_1107_);
return v___x_1108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* v_word_1113_, lean_object* v_pattern_1114_, lean_object* v_patternRoles_1115_, lean_object* v_wordRoles_1116_, lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v_range_1121_, lean_object* v_b_1122_, lean_object* v_i_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1113_, v_pattern_1114_, v_patternRoles_1115_, v_wordRoles_1116_, v___x_1117_, v___x_1118_, v___x_1119_, v___x_1120_, v_range_1121_, v_b_1122_, v_i_1123_);
lean_dec_ref(v_range_1121_);
lean_dec(v___x_1120_);
lean_dec(v___x_1119_);
lean_dec(v___x_1118_);
lean_dec_ref(v___x_1117_);
lean_dec_ref(v_wordRoles_1116_);
lean_dec_ref(v_patternRoles_1115_);
lean_dec_ref(v_pattern_1114_);
lean_dec_ref(v_word_1113_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* v_wordRoles_1125_, lean_object* v_range_1126_, lean_object* v_b_1127_, lean_object* v_i_1128_){
_start:
{
lean_object* v_stop_1129_; lean_object* v_step_1130_; uint8_t v___x_1131_; 
v_stop_1129_ = lean_ctor_get(v_range_1126_, 1);
v_step_1130_ = lean_ctor_get(v_range_1126_, 2);
v___x_1131_ = lean_nat_dec_lt(v_i_1128_, v_stop_1129_);
if (v___x_1131_ == 0)
{
lean_dec(v_i_1128_);
return v_b_1127_;
}
else
{
lean_object* v_snd_1132_; lean_object* v_snd_1133_; lean_object* v_fst_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1190_; 
v_snd_1132_ = lean_ctor_get(v_b_1127_, 1);
lean_inc(v_snd_1132_);
v_snd_1133_ = lean_ctor_get(v_snd_1132_, 1);
lean_inc(v_snd_1133_);
v_fst_1134_ = lean_ctor_get(v_b_1127_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_b_1127_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_b_1127_, 1);
lean_dec(v_unused_1191_);
v___x_1136_ = v_b_1127_;
v_isShared_1137_ = v_isSharedCheck_1190_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_fst_1134_);
lean_dec(v_b_1127_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1190_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fst_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1188_; 
v_fst_1138_ = lean_ctor_get(v_snd_1132_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_snd_1132_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_snd_1132_, 1);
lean_dec(v_unused_1189_);
v___x_1140_ = v_snd_1132_;
v_isShared_1141_ = v_isSharedCheck_1188_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_fst_1138_);
lean_dec(v_snd_1132_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1188_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1187_; 
v_fst_1142_ = lean_ctor_get(v_snd_1133_, 0);
v_snd_1143_ = lean_ctor_get(v_snd_1133_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_snd_1133_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1145_ = v_snd_1133_;
v_isShared_1146_ = v_isSharedCheck_1187_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_dec(v_snd_1133_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1187_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
uint8_t v___x_1147_; lean_object* v_lastSepIdx_1148_; lean_object* v_lastSepIdx_1150_; uint16_t v_penaltyNs_1151_; uint16_t v_penaltySkip_1152_; uint8_t v___x_1175_; 
v___x_1147_ = 0;
v_lastSepIdx_1148_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_nat_dec_eq(v_i_1128_, v_lastSepIdx_1148_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_box(v___x_1147_);
v___x_1177_ = lean_array_get(v___x_1176_, v_wordRoles_1125_, v_i_1128_);
lean_dec(v___x_1176_);
v___x_1178_ = lean_unbox(v___x_1177_);
lean_dec(v___x_1177_);
if (v___x_1178_ == 2)
{
uint16_t v_penaltyNs_1179_; uint16_t v___x_1180_; uint16_t v___x_1181_; uint16_t v___x_1182_; 
lean_dec(v_snd_1143_);
lean_dec(v_fst_1138_);
v_penaltyNs_1179_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1180_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1181_ = lean_unbox(v_fst_1142_);
lean_dec(v_fst_1142_);
v___x_1182_ = lean_int16_add(v___x_1181_, v___x_1180_);
lean_inc(v_i_1128_);
v_lastSepIdx_1150_ = v_i_1128_;
v_penaltyNs_1151_ = v___x_1182_;
v_penaltySkip_1152_ = v_penaltyNs_1179_;
goto v___jp_1149_;
}
else
{
uint16_t v___x_1183_; uint16_t v___x_1184_; 
v___x_1183_ = lean_unbox(v_fst_1142_);
lean_dec(v_fst_1142_);
v___x_1184_ = lean_unbox(v_snd_1143_);
lean_dec(v_snd_1143_);
v_lastSepIdx_1150_ = v_fst_1138_;
v_penaltyNs_1151_ = v___x_1183_;
v_penaltySkip_1152_ = v___x_1184_;
goto v___jp_1149_;
}
}
else
{
uint16_t v___x_1185_; uint16_t v___x_1186_; 
v___x_1185_ = lean_unbox(v_fst_1142_);
lean_dec(v_fst_1142_);
v___x_1186_ = lean_unbox(v_snd_1143_);
lean_dec(v_snd_1143_);
v_lastSepIdx_1150_ = v_fst_1138_;
v_penaltyNs_1151_ = v___x_1185_;
v_penaltySkip_1152_ = v___x_1186_;
goto v___jp_1149_;
}
v___jp_1149_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; uint8_t v___x_1156_; uint16_t v___x_1157_; uint16_t v___x_1158_; uint16_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1153_ = lean_box(v___x_1147_);
v___x_1154_ = lean_array_get(v___x_1153_, v_wordRoles_1125_, v_i_1128_);
lean_dec(v___x_1153_);
v___x_1155_ = lean_nat_dec_eq(v_i_1128_, v_lastSepIdx_1148_);
v___x_1156_ = lean_unbox(v___x_1154_);
lean_dec(v___x_1154_);
v___x_1157_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_1156_, v___x_1155_);
v___x_1158_ = lean_int16_add(v_penaltySkip_1152_, v___x_1157_);
v___x_1159_ = lean_int16_add(v___x_1158_, v_penaltyNs_1151_);
v___x_1160_ = lean_box(v___x_1159_);
v___x_1161_ = lean_array_set(v_fst_1134_, v_i_1128_, v___x_1160_);
v___x_1162_ = lean_box(v_penaltyNs_1151_);
v___x_1163_ = lean_box(v___x_1158_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1163_);
lean_ctor_set(v___x_1145_, 0, v___x_1162_);
v___x_1165_ = v___x_1145_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1165_);
lean_ctor_set(v___x_1140_, 0, v_lastSepIdx_1150_);
v___x_1167_ = v___x_1140_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_lastSepIdx_1150_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1167_);
lean_ctor_set(v___x_1136_, 0, v___x_1161_);
v___x_1169_ = v___x_1136_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_nat_add(v_i_1128_, v_step_1130_);
lean_dec(v_i_1128_);
v_b_1127_ = v___x_1169_;
v_i_1128_ = v___x_1170_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* v_wordRoles_1192_, lean_object* v_range_1193_, lean_object* v_b_1194_, lean_object* v_i_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1192_, v_range_1193_, v_b_1194_, v_i_1195_);
lean_dec_ref(v_range_1193_);
lean_dec_ref(v_wordRoles_1192_);
return v_res_1196_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0(void){
_start:
{
uint16_t v_penaltyNs_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_penaltyNs_1197_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1198_ = lean_box(v_penaltyNs_1197_);
v___x_1199_ = lean_box(v_penaltyNs_1197_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
return v___x_1200_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1(void){
_start:
{
lean_object* v___x_1201_; lean_object* v_lastSepIdx_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
v_lastSepIdx_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_lastSepIdx_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* v_pattern_1204_, lean_object* v_word_1205_, lean_object* v_patternRoles_1206_, lean_object* v_wordRoles_1207_){
_start:
{
uint16_t v___y_1209_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_lastSepIdx_1220_; uint16_t v_penaltyNs_1221_; lean_object* v___x_1222_; lean_object* v_runLengths_1223_; lean_object* v___x_1224_; lean_object* v_startPenalties_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_snd_1231_; lean_object* v_fst_1232_; lean_object* v_fst_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1263_; 
v___x_1215_ = lean_string_length(v_pattern_1204_);
v___x_1216_ = lean_string_length(v_word_1205_);
v___x_1217_ = lean_nat_mul(v___x_1215_, v___x_1216_);
v___x_1218_ = lean_unsigned_to_nat(2u);
v___x_1219_ = lean_nat_mul(v___x_1217_, v___x_1218_);
v_lastSepIdx_1220_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1221_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1222_ = lean_box(v_penaltyNs_1221_);
v_runLengths_1223_ = lean_mk_array(v___x_1217_, v___x_1222_);
v___x_1224_ = lean_box(v_penaltyNs_1221_);
v_startPenalties_1225_ = lean_mk_array(v___x_1216_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1227_, 0, v_lastSepIdx_1220_);
lean_ctor_set(v___x_1227_, 1, v___x_1216_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
v___x_1228_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_startPenalties_1225_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1207_, v___x_1227_, v___x_1229_, v_lastSepIdx_1220_);
lean_dec_ref_known(v___x_1227_, 3);
v_snd_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_snd_1231_);
v_fst_1232_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_fst_1232_);
lean_dec_ref(v___x_1230_);
v_fst_1233_ = lean_ctor_get(v_snd_1231_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_snd_1231_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v_snd_1231_, 1);
lean_dec(v_unused_1264_);
v___x_1235_ = v_snd_1231_;
v_isShared_1236_ = v_isSharedCheck_1263_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_fst_1233_);
lean_dec(v_snd_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1263_;
goto v_resetjp_1234_;
}
v___jp_1208_:
{
uint16_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1211_ = lean_int16_dec_le(v___y_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_int16_to_int(v___y_1209_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_box(0);
return v___x_1214_;
}
}
v_resetjp_1234_:
{
uint16_t v_matchScore_1237_; lean_object* v___x_1238_; lean_object* v_result_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v_matchScore_1237_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1238_ = lean_box(v_matchScore_1237_);
v_result_1239_ = lean_mk_array(v___x_1219_, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1240_, 0, v_lastSepIdx_1220_);
lean_ctor_set(v___x_1240_, 1, v___x_1215_);
lean_ctor_set(v___x_1240_, 2, v___x_1226_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_runLengths_1223_);
lean_ctor_set(v___x_1235_, 0, v_result_1239_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_result_1239_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_runLengths_1223_);
v___x_1242_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v_fst_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint16_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint16_t v___x_1257_; uint16_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1243_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1205_, v_pattern_1204_, v_patternRoles_1206_, v_wordRoles_1207_, v_fst_1232_, v_fst_1233_, v___x_1215_, v___x_1216_, v___x_1240_, v___x_1242_, v_lastSepIdx_1220_);
lean_dec_ref_known(v___x_1240_, 3);
lean_dec(v_fst_1233_);
lean_dec(v_fst_1232_);
v_fst_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = lean_nat_sub(v___x_1215_, v___x_1226_);
v___x_1246_ = lean_nat_sub(v___x_1216_, v___x_1226_);
v___x_1247_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1248_ = lean_nat_mul(v___x_1245_, v___x_1216_);
lean_dec(v___x_1245_);
v___x_1249_ = lean_nat_mul(v___x_1248_, v___x_1218_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_nat_mul(v___x_1246_, v___x_1218_);
lean_dec(v___x_1246_);
v___x_1251_ = lean_nat_add(v___x_1249_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(v___x_1247_);
v___x_1253_ = lean_array_get(v___x_1252_, v_fst_1244_, v___x_1251_);
lean_dec(v___x_1252_);
v___x_1254_ = lean_nat_add(v___x_1251_, v___x_1226_);
lean_dec(v___x_1251_);
v___x_1255_ = lean_box(v___x_1247_);
v___x_1256_ = lean_array_get(v___x_1255_, v_fst_1244_, v___x_1254_);
lean_dec(v___x_1254_);
lean_dec(v_fst_1244_);
lean_dec(v___x_1255_);
v___x_1257_ = lean_unbox(v___x_1253_);
v___x_1258_ = lean_unbox(v___x_1256_);
v___x_1259_ = lean_int16_dec_le(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
uint16_t v___x_1260_; 
lean_dec(v___x_1256_);
v___x_1260_ = lean_unbox(v___x_1253_);
lean_dec(v___x_1253_);
v___y_1209_ = v___x_1260_;
goto v___jp_1208_;
}
else
{
uint16_t v___x_1261_; 
lean_dec(v___x_1253_);
v___x_1261_ = lean_unbox(v___x_1256_);
lean_dec(v___x_1256_);
v___y_1209_ = v___x_1261_;
goto v___jp_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* v_pattern_1265_, lean_object* v_word_1266_, lean_object* v_patternRoles_1267_, lean_object* v_wordRoles_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1265_, v_word_1266_, v_patternRoles_1267_, v_wordRoles_1268_);
lean_dec_ref(v_wordRoles_1268_);
lean_dec_ref(v_patternRoles_1267_);
lean_dec_ref(v_word_1266_);
lean_dec_ref(v_pattern_1265_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* v_wordRoles_1270_, lean_object* v_range_1271_, lean_object* v_b_1272_, lean_object* v_i_1273_, lean_object* v_hs_1274_, lean_object* v_hl_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1270_, v_range_1271_, v_b_1272_, v_i_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* v_wordRoles_1277_, lean_object* v_range_1278_, lean_object* v_b_1279_, lean_object* v_i_1280_, lean_object* v_hs_1281_, lean_object* v_hl_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_1277_, v_range_1278_, v_b_1279_, v_i_1280_, v_hs_1281_, v_hl_1282_);
lean_dec_ref(v_range_1278_);
lean_dec_ref(v_wordRoles_1277_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* v_word_1284_, lean_object* v_a_1285_, lean_object* v_pattern_1286_, lean_object* v_patternRoles_1287_, lean_object* v_wordRoles_1288_, lean_object* v___x_1289_, lean_object* v___x_1290_, lean_object* v_range_1291_, lean_object* v_b_1292_, lean_object* v_i_1293_, lean_object* v_hs_1294_, lean_object* v_hl_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1284_, v_a_1285_, v_pattern_1286_, v_patternRoles_1287_, v_wordRoles_1288_, v___x_1289_, v___x_1290_, v_range_1291_, v_b_1292_, v_i_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* v_word_1297_, lean_object* v_a_1298_, lean_object* v_pattern_1299_, lean_object* v_patternRoles_1300_, lean_object* v_wordRoles_1301_, lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v_range_1304_, lean_object* v_b_1305_, lean_object* v_i_1306_, lean_object* v_hs_1307_, lean_object* v_hl_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v_word_1297_, v_a_1298_, v_pattern_1299_, v_patternRoles_1300_, v_wordRoles_1301_, v___x_1302_, v___x_1303_, v_range_1304_, v_b_1305_, v_i_1306_, v_hs_1307_, v_hl_1308_);
lean_dec_ref(v_range_1304_);
lean_dec(v___x_1303_);
lean_dec_ref(v___x_1302_);
lean_dec_ref(v_wordRoles_1301_);
lean_dec_ref(v_patternRoles_1300_);
lean_dec_ref(v_pattern_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_word_1297_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* v_word_1310_, lean_object* v_pattern_1311_, lean_object* v_patternRoles_1312_, lean_object* v_wordRoles_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v_range_1318_, lean_object* v_b_1319_, lean_object* v_i_1320_, lean_object* v_hs_1321_, lean_object* v_hl_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1310_, v_pattern_1311_, v_patternRoles_1312_, v_wordRoles_1313_, v___x_1314_, v___x_1315_, v___x_1316_, v___x_1317_, v_range_1318_, v_b_1319_, v_i_1320_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* v_word_1324_, lean_object* v_pattern_1325_, lean_object* v_patternRoles_1326_, lean_object* v_wordRoles_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v_range_1332_, lean_object* v_b_1333_, lean_object* v_i_1334_, lean_object* v_hs_1335_, lean_object* v_hl_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v_word_1324_, v_pattern_1325_, v_patternRoles_1326_, v_wordRoles_1327_, v___x_1328_, v___x_1329_, v___x_1330_, v___x_1331_, v_range_1332_, v_b_1333_, v_i_1334_, v_hs_1335_, v_hl_1336_);
lean_dec_ref(v_range_1332_);
lean_dec(v___x_1331_);
lean_dec(v___x_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1328_);
lean_dec_ref(v_wordRoles_1327_);
lean_dec_ref(v_patternRoles_1326_);
lean_dec_ref(v_pattern_1325_);
lean_dec_ref(v_word_1324_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object* v___x_1338_, lean_object* v___x_1339_, lean_object* v_word_1340_, lean_object* v_pattern_1341_, lean_object* v_patternRoles_1342_, lean_object* v_wordRoles_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_range_1346_, lean_object* v_b_1347_, lean_object* v_i_1348_, lean_object* v_hs_1349_, lean_object* v_hl_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1338_, v___x_1339_, v_word_1340_, v_pattern_1341_, v_patternRoles_1342_, v_wordRoles_1343_, v___x_1344_, v___x_1345_, v_range_1346_, v_b_1347_, v_i_1348_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object* v___x_1352_, lean_object* v___x_1353_, lean_object* v_word_1354_, lean_object* v_pattern_1355_, lean_object* v_patternRoles_1356_, lean_object* v_wordRoles_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v_range_1360_, lean_object* v_b_1361_, lean_object* v_i_1362_, lean_object* v_hs_1363_, lean_object* v_hl_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(v___x_1352_, v___x_1353_, v_word_1354_, v_pattern_1355_, v_patternRoles_1356_, v_wordRoles_1357_, v___x_1358_, v___x_1359_, v_range_1360_, v_b_1361_, v_i_1362_, v_hs_1363_, v_hl_1364_);
lean_dec_ref(v_range_1360_);
lean_dec(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v_wordRoles_1357_);
lean_dec_ref(v_patternRoles_1356_);
lean_dec_ref(v_pattern_1355_);
lean_dec_ref(v_word_1354_);
lean_dec(v___x_1353_);
lean_dec(v___x_1352_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_nat_to_int(v_a_1366_);
return v___x_1367_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1368_; double v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_float_of_nat(v___x_1368_);
return v___x_1369_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1(void){
_start:
{
lean_object* v___x_1370_; double v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_float_of_nat(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_unsigned_to_nat(2u);
v___x_1373_ = lean_nat_to_int(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1(void){
_start:
{
double v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1375_ = lean_box_float(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* v_pattern_1378_, lean_object* v_word_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1380_ = lean_string_utf8_byte_size(v_pattern_1378_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_nat_dec_eq(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_score_1386_; uint8_t v___x_1405_; 
v___x_1383_ = lean_string_length(v_word_1379_);
v___x_1384_ = lean_string_length(v_pattern_1378_);
v___x_1405_ = lean_nat_dec_lt(v___x_1383_, v___x_1384_);
if (v___x_1405_ == 0)
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_String_charactersIn(v_pattern_1378_, v_word_1379_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_box(0);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_1378_);
v___x_1409_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_1379_);
v___x_1410_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1378_, v_word_1379_, v___x_1408_, v___x_1409_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v___x_1408_);
if (lean_obj_tag(v___x_1410_) == 1)
{
lean_object* v_val_1411_; uint8_t v___x_1412_; 
v_val_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = lean_nat_dec_eq(v___x_1384_, v___x_1383_);
if (v___x_1412_ == 0)
{
v_score_1386_ = v_val_1411_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1413_; lean_object* v_score_1414_; 
v___x_1413_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
v_score_1414_ = lean_int_mul(v_val_1411_, v___x_1413_);
lean_dec(v_val_1411_);
v_score_1386_ = v_score_1414_;
goto v___jp_1385_;
}
}
else
{
lean_object* v___x_1415_; 
lean_dec(v___x_1410_);
v___x_1415_ = lean_box(0);
return v___x_1415_;
}
}
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
v___jp_1385_:
{
lean_object* v_perfect_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_perfectMatch_1394_; double v___x_1395_; lean_object* v___x_1396_; double v___x_1397_; double v_normScore_1398_; double v___x_1399_; double v___x_1400_; double v___x_1401_; double v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_perfect_1387_ = lean_unsigned_to_nat(4u);
v___x_1388_ = lean_nat_mul(v_perfect_1387_, v___x_1384_);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v___x_1384_, v___x_1389_);
v___x_1391_ = lean_nat_mul(v___x_1384_, v___x_1390_);
lean_dec(v___x_1390_);
v___x_1392_ = lean_nat_shiftr(v___x_1391_, v___x_1389_);
lean_dec(v___x_1391_);
v___x_1393_ = lean_nat_sub(v___x_1392_, v___x_1389_);
lean_dec(v___x_1392_);
v_perfectMatch_1394_ = lean_nat_add(v___x_1388_, v___x_1393_);
lean_dec(v___x_1393_);
lean_dec(v___x_1388_);
v___x_1395_ = l_Float_ofInt(v_score_1386_);
lean_dec(v_score_1386_);
v___x_1396_ = lean_nat_to_int(v_perfectMatch_1394_);
v___x_1397_ = l_Float_ofInt(v___x_1396_);
lean_dec(v___x_1396_);
v_normScore_1398_ = lean_float_div(v___x_1395_, v___x_1397_);
v___x_1399_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1400_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1);
v___x_1401_ = lean_float_maximum(v___x_1400_, v_normScore_1398_);
v___x_1402_ = lean_float_minimum(v___x_1399_, v___x_1401_);
v___x_1403_ = lean_box_float(v___x_1402_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* v_pattern_1418_, lean_object* v_word_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1418_, v_word_1419_);
lean_dec_ref(v_word_1419_);
lean_dec_ref(v_pattern_1418_);
return v_res_1420_;
}
}
lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* v_pattern_1421_, lean_object* v_word_1422_, double v_threshold_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1421_, v_word_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
return v___x_1424_;
}
else
{
lean_object* v_val_1425_; double v___x_1426_; uint8_t v___x_1427_; 
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
v___x_1426_ = lean_unbox_float(v_val_1425_);
v___x_1427_ = lean_float_decLt(v_threshold_1423_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
lean_dec_ref_known(v___x_1424_, 1);
v___x_1428_ = lean_box(0);
return v___x_1428_;
}
else
{
return v___x_1424_;
}
}
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_1421_ = stack[0].m_obj;
lean_object* v_word_1422_ = stack[1].m_obj;
double v_threshold_1423_ = stack[2].m_float;
lean_object* v_res_1429_;
v_res_1429_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1421_, v_word_1422_, v_threshold_1423_);
stack->m_obj
 = v_res_1429_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* v_pattern_1430_, lean_object* v_word_1431_, lean_object* v_threshold_1432_){
_start:
{
double v_threshold_boxed_1433_; lean_object* v_res_1434_; 
v_threshold_boxed_1433_ = lean_unbox_float(v_threshold_1432_);
lean_dec_ref(v_threshold_1432_);
v_res_1434_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1430_, v_word_1431_, v_threshold_boxed_1433_);
lean_dec_ref(v_word_1431_);
lean_dec_ref(v_pattern_1430_);
return v_res_1434_;
}
}
uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* v_pattern_1435_, lean_object* v_word_1436_, double v_threshold_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1435_, v_word_1436_, v_threshold_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
uint8_t v___x_1439_; 
v___x_1439_ = 0;
return v___x_1439_;
}
else
{
uint8_t v___x_1440_; 
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = 1;
return v___x_1440_;
}
}
}
LEAN_EXPORT void l_Lean_FuzzyMatching_fuzzyMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_1435_ = stack[0].m_obj;
lean_object* v_word_1436_ = stack[1].m_obj;
double v_threshold_1437_ = stack[2].m_float;
uint8_t v_res_1441_;
v_res_1441_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1435_, v_word_1436_, v_threshold_1437_);
stack->m_num = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* v_pattern_1442_, lean_object* v_word_1443_, lean_object* v_threshold_1444_){
_start:
{
double v_threshold_boxed_1445_; uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_threshold_boxed_1445_ = lean_unbox_float(v_threshold_1444_);
lean_dec_ref(v_threshold_1444_);
v_res_1446_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1442_, v_word_1443_, v_threshold_boxed_1445_);
lean_dec_ref(v_word_1443_);
lean_dec_ref(v_pattern_1442_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
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
