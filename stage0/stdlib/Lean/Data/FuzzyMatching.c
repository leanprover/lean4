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
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___impl(uint8_t v_x_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_box(v_x_136_);
v___x_138_ = lean_obj_tag_nat(v___x_137_);
lean_dec(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorIdx___impl___boxed(lean_object* v_x_139_){
_start:
{
uint8_t v_x_4__boxed_140_; lean_object* v_res_141_; 
v_x_4__boxed_140_ = lean_unbox(v_x_139_);
v_res_141_ = l_Lean_FuzzyMatching_CharType_ctorIdx___impl(v_x_4__boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg(lean_object* v_k_142_){
_start:
{
lean_inc(v_k_142_);
return v_k_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(lean_object* v_k_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_FuzzyMatching_CharType_ctorElim___redArg(v_k_143_);
lean_dec(v_k_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim(lean_object* v_motive_145_, lean_object* v_ctorIdx_146_, uint8_t v_t_147_, lean_object* v_h_148_, lean_object* v_k_149_){
_start:
{
lean_inc(v_k_149_);
return v_k_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_ctorElim___boxed(lean_object* v_motive_150_, lean_object* v_ctorIdx_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_k_154_){
_start:
{
uint8_t v_t_boxed_155_; lean_object* v_res_156_; 
v_t_boxed_155_ = lean_unbox(v_t_152_);
v_res_156_ = l_Lean_FuzzyMatching_CharType_ctorElim(v_motive_150_, v_ctorIdx_151_, v_t_boxed_155_, v_h_153_, v_k_154_);
lean_dec(v_k_154_);
lean_dec(v_ctorIdx_151_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg(lean_object* v_lower_157_){
_start:
{
lean_inc(v_lower_157_);
return v_lower_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(lean_object* v_lower_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_FuzzyMatching_CharType_lower_elim___redArg(v_lower_158_);
lean_dec(v_lower_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim(lean_object* v_motive_160_, uint8_t v_t_161_, lean_object* v_h_162_, lean_object* v_lower_163_){
_start:
{
lean_inc(v_lower_163_);
return v_lower_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_lower_elim___boxed(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_lower_167_){
_start:
{
uint8_t v_t_boxed_168_; lean_object* v_res_169_; 
v_t_boxed_168_ = lean_unbox(v_t_165_);
v_res_169_ = l_Lean_FuzzyMatching_CharType_lower_elim(v_motive_164_, v_t_boxed_168_, v_h_166_, v_lower_167_);
lean_dec(v_lower_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg(lean_object* v_upper_170_){
_start:
{
lean_inc(v_upper_170_);
return v_upper_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(lean_object* v_upper_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_FuzzyMatching_CharType_upper_elim___redArg(v_upper_171_);
lean_dec(v_upper_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim(lean_object* v_motive_173_, uint8_t v_t_174_, lean_object* v_h_175_, lean_object* v_upper_176_){
_start:
{
lean_inc(v_upper_176_);
return v_upper_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_upper_elim___boxed(lean_object* v_motive_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_upper_180_){
_start:
{
uint8_t v_t_boxed_181_; lean_object* v_res_182_; 
v_t_boxed_181_ = lean_unbox(v_t_178_);
v_res_182_ = l_Lean_FuzzyMatching_CharType_upper_elim(v_motive_177_, v_t_boxed_181_, v_h_179_, v_upper_180_);
lean_dec(v_upper_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg(lean_object* v_separator_183_){
_start:
{
lean_inc(v_separator_183_);
return v_separator_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___redArg___boxed(lean_object* v_separator_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_FuzzyMatching_CharType_separator_elim___redArg(v_separator_184_);
lean_dec(v_separator_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim(lean_object* v_motive_186_, uint8_t v_t_187_, lean_object* v_h_188_, lean_object* v_separator_189_){
_start:
{
lean_inc(v_separator_189_);
return v_separator_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharType_separator_elim___boxed(lean_object* v_motive_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_separator_193_){
_start:
{
uint8_t v_t_boxed_194_; lean_object* v_res_195_; 
v_t_boxed_194_ = lean_unbox(v_t_191_);
v_res_195_ = l_Lean_FuzzyMatching_CharType_separator_elim(v_motive_190_, v_t_boxed_194_, v_h_192_, v_separator_193_);
lean_dec(v_separator_193_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charType(uint32_t v_c_196_){
_start:
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 65;
v___x_218_ = lean_uint32_dec_le(v___x_217_, v_c_196_);
if (v___x_218_ == 0)
{
goto v___jp_212_;
}
else
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 90;
v___x_220_ = lean_uint32_dec_le(v_c_196_, v___x_219_);
if (v___x_220_ == 0)
{
goto v___jp_212_;
}
else
{
goto v___jp_197_;
}
}
v___jp_197_:
{
uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = 65;
v___x_199_ = lean_uint32_dec_le(v___x_198_, v_c_196_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
else
{
uint32_t v___x_201_; uint8_t v___x_202_; 
v___x_201_ = 90;
v___x_202_ = lean_uint32_dec_le(v_c_196_, v___x_201_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 1;
return v___x_204_;
}
}
}
v___jp_205_:
{
uint32_t v___x_206_; uint8_t v___x_207_; 
v___x_206_ = 48;
v___x_207_ = lean_uint32_dec_le(v___x_206_, v_c_196_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; 
v___x_208_ = 2;
return v___x_208_;
}
else
{
uint32_t v___x_209_; uint8_t v___x_210_; 
v___x_209_ = 57;
v___x_210_ = lean_uint32_dec_le(v_c_196_, v___x_209_);
if (v___x_210_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 2;
return v___x_211_;
}
else
{
goto v___jp_197_;
}
}
}
v___jp_212_:
{
uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_213_ = 97;
v___x_214_ = lean_uint32_dec_le(v___x_213_, v_c_196_);
if (v___x_214_ == 0)
{
goto v___jp_205_;
}
else
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 122;
v___x_216_ = lean_uint32_dec_le(v_c_196_, v___x_215_);
if (v___x_216_ == 0)
{
goto v___jp_205_;
}
else
{
goto v___jp_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charType___boxed(lean_object* v_c_221_){
_start:
{
uint32_t v_c_boxed_222_; uint8_t v_res_223_; lean_object* v_r_224_; 
v_c_boxed_222_ = lean_unbox_uint32(v_c_221_);
lean_dec(v_c_221_);
v_res_223_ = l_Lean_FuzzyMatching_charType(v_c_boxed_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___impl(uint8_t v_x_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(v_x_225_);
v___x_227_ = lean_obj_tag_nat(v___x_226_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorIdx___impl___boxed(lean_object* v_x_228_){
_start:
{
uint8_t v_x_4__boxed_229_; lean_object* v_res_230_; 
v_x_4__boxed_229_ = lean_unbox(v_x_228_);
v_res_230_ = l_Lean_FuzzyMatching_CharRole_ctorIdx___impl(v_x_4__boxed_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(lean_object* v_k_231_){
_start:
{
lean_inc(v_k_231_);
return v_k_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(lean_object* v_k_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(v_k_232_);
lean_dec(v_k_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim(lean_object* v_motive_234_, lean_object* v_ctorIdx_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_k_238_){
_start:
{
lean_inc(v_k_238_);
return v_k_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(lean_object* v_motive_239_, lean_object* v_ctorIdx_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_k_243_){
_start:
{
uint8_t v_t_boxed_244_; lean_object* v_res_245_; 
v_t_boxed_244_ = lean_unbox(v_t_241_);
v_res_245_ = l_Lean_FuzzyMatching_CharRole_ctorElim(v_motive_239_, v_ctorIdx_240_, v_t_boxed_244_, v_h_242_, v_k_243_);
lean_dec(v_k_243_);
lean_dec(v_ctorIdx_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg(lean_object* v_head_246_){
_start:
{
lean_inc(v_head_246_);
return v_head_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(lean_object* v_head_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(v_head_247_);
lean_dec(v_head_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim(lean_object* v_motive_249_, uint8_t v_t_250_, lean_object* v_h_251_, lean_object* v_head_252_){
_start:
{
lean_inc(v_head_252_);
return v_head_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_head_elim___boxed(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_head_256_){
_start:
{
uint8_t v_t_boxed_257_; lean_object* v_res_258_; 
v_t_boxed_257_ = lean_unbox(v_t_254_);
v_res_258_ = l_Lean_FuzzyMatching_CharRole_head_elim(v_motive_253_, v_t_boxed_257_, v_h_255_, v_head_256_);
lean_dec(v_head_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(lean_object* v_tail_259_){
_start:
{
lean_inc(v_tail_259_);
return v_tail_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(lean_object* v_tail_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(v_tail_260_);
lean_dec(v_tail_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim(lean_object* v_motive_262_, uint8_t v_t_263_, lean_object* v_h_264_, lean_object* v_tail_265_){
_start:
{
lean_inc(v_tail_265_);
return v_tail_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_tail_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_FuzzyMatching_CharRole_tail_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_tail_269_);
lean_dec(v_tail_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(lean_object* v_separator_272_){
_start:
{
lean_inc(v_separator_272_);
return v_separator_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(lean_object* v_separator_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(v_separator_273_);
lean_dec(v_separator_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_separator_278_){
_start:
{
lean_inc(v_separator_278_);
return v_separator_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_separator_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_FuzzyMatching_CharRole_separator_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_separator_282_);
lean_dec(v_separator_282_);
return v_res_284_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default(void){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_instInhabitedCharRole(void){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object* v_prev_x3f_287_, uint8_t v_curr_288_, lean_object* v_next_x3f_289_){
_start:
{
if (v_curr_288_ == 2)
{
uint8_t v___x_290_; 
v___x_290_ = 2;
return v___x_290_;
}
else
{
if (lean_obj_tag(v_prev_x3f_287_) == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 0;
return v___x_291_;
}
else
{
lean_object* v_val_292_; uint8_t v___x_293_; 
v_val_292_ = lean_ctor_get(v_prev_x3f_287_, 0);
v___x_293_ = lean_unbox(v_val_292_);
if (v___x_293_ == 2)
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
else
{
if (v_curr_288_ == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 1;
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = lean_unbox(v_val_292_);
if (v___x_296_ == 1)
{
if (lean_obj_tag(v_next_x3f_289_) == 1)
{
lean_object* v_val_297_; uint8_t v___x_298_; 
v_val_297_ = lean_ctor_get(v_next_x3f_289_, 0);
v___x_298_ = lean_unbox(v_val_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = 1;
return v___x_300_;
}
}
else
{
uint8_t v___x_301_; 
v___x_301_ = 1;
return v___x_301_;
}
}
else
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object* v_prev_x3f_303_, lean_object* v_curr_304_, lean_object* v_next_x3f_305_){
_start:
{
uint8_t v_curr_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_curr_boxed_306_ = lean_unbox(v_curr_304_);
v_res_307_ = l_Lean_FuzzyMatching_charRole(v_prev_x3f_303_, v_curr_boxed_306_, v_next_x3f_305_);
lean_dec(v_next_x3f_305_);
lean_dec(v_prev_x3f_303_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_string_309_, lean_object* v_range_310_, lean_object* v_b_311_, lean_object* v_i_312_){
_start:
{
lean_object* v_stop_313_; lean_object* v_step_314_; uint8_t v___y_316_; uint8_t v___x_321_; 
v_stop_313_ = lean_ctor_get(v_range_310_, 1);
v_step_314_ = lean_ctor_get(v_range_310_, 2);
v___x_321_ = lean_nat_dec_lt(v_i_312_, v_stop_313_);
if (v___x_321_ == 0)
{
lean_dec(v_i_312_);
return v_b_311_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_sub(v_i_312_, v___x_322_);
v___x_324_ = lean_string_utf8_get(v_string_309_, v___x_323_);
lean_dec(v___x_323_);
v___x_325_ = l_Lean_FuzzyMatching_charType(v___x_324_);
if (v___x_325_ == 2)
{
uint8_t v___x_326_; 
v___x_326_ = 2;
v___y_316_ = v___x_326_;
goto v___jp_315_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; uint32_t v___x_329_; uint8_t v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = lean_nat_sub(v_i_312_, v___x_327_);
v___x_329_ = lean_string_utf8_get(v_string_309_, v___x_328_);
lean_dec(v___x_328_);
v___x_330_ = l_Lean_FuzzyMatching_charType(v___x_329_);
if (v___x_330_ == 2)
{
uint8_t v___x_331_; 
v___x_331_ = 0;
v___y_316_ = v___x_331_;
goto v___jp_315_;
}
else
{
if (v___x_325_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = 1;
v___y_316_ = v___x_332_;
goto v___jp_315_;
}
else
{
if (v___x_330_ == 1)
{
uint32_t v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_string_utf8_get(v_string_309_, v_i_312_);
v___x_334_ = l_Lean_FuzzyMatching_charType(v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = 0;
v___y_316_ = v___x_335_;
goto v___jp_315_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = 1;
v___y_316_ = v___x_336_;
goto v___jp_315_;
}
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 0;
v___y_316_ = v___x_337_;
goto v___jp_315_;
}
}
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(v___y_316_);
v___x_318_ = lean_array_push(v_b_311_, v___x_317_);
v___x_319_ = lean_nat_add(v_i_312_, v_step_314_);
lean_dec(v_i_312_);
v_b_311_ = v___x_318_;
v_i_312_ = v___x_319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_string_338_, lean_object* v_range_339_, lean_object* v_b_340_, lean_object* v_i_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_338_, v_range_339_, v_b_340_, v_i_341_);
lean_dec_ref(v_range_339_);
lean_dec_ref(v_string_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object* v_string_343_, lean_object* v_range_344_, lean_object* v_b_345_, lean_object* v_i_346_){
_start:
{
lean_object* v_stop_347_; lean_object* v_step_348_; uint8_t v___y_350_; uint8_t v___x_355_; 
v_stop_347_ = lean_ctor_get(v_range_344_, 1);
v_step_348_ = lean_ctor_get(v_range_344_, 2);
v___x_355_ = lean_nat_dec_lt(v_i_346_, v_stop_347_);
if (v___x_355_ == 0)
{
return v_b_345_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_sub(v_i_346_, v___x_356_);
v___x_358_ = lean_string_utf8_get(v_string_343_, v___x_357_);
lean_dec(v___x_357_);
v___x_359_ = l_Lean_FuzzyMatching_charType(v___x_358_);
if (v___x_359_ == 2)
{
uint8_t v___x_360_; 
v___x_360_ = 2;
v___y_350_ = v___x_360_;
goto v___jp_349_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_361_ = lean_unsigned_to_nat(2u);
v___x_362_ = lean_nat_sub(v_i_346_, v___x_361_);
v___x_363_ = lean_string_utf8_get(v_string_343_, v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = l_Lean_FuzzyMatching_charType(v___x_363_);
if (v___x_364_ == 2)
{
uint8_t v___x_365_; 
v___x_365_ = 0;
v___y_350_ = v___x_365_;
goto v___jp_349_;
}
else
{
if (v___x_359_ == 0)
{
uint8_t v___x_366_; 
v___x_366_ = 1;
v___y_350_ = v___x_366_;
goto v___jp_349_;
}
else
{
if (v___x_364_ == 1)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_string_utf8_get(v_string_343_, v_i_346_);
v___x_368_ = l_Lean_FuzzyMatching_charType(v___x_367_);
if (v___x_368_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = 0;
v___y_350_ = v___x_369_;
goto v___jp_349_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 1;
v___y_350_ = v___x_370_;
goto v___jp_349_;
}
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 0;
v___y_350_ = v___x_371_;
goto v___jp_349_;
}
}
}
}
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = lean_box(v___y_350_);
v___x_352_ = lean_array_push(v_b_345_, v___x_351_);
v___x_353_ = lean_nat_add(v_i_346_, v_step_348_);
v___x_354_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_343_, v_range_344_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object* v_string_372_, lean_object* v_range_373_, lean_object* v_b_374_, lean_object* v_i_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_372_, v_range_373_, v_b_374_, v_i_375_);
lean_dec(v_i_375_);
lean_dec_ref(v_range_373_);
lean_dec_ref(v_string_372_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(lean_object* v_prev_x3f_377_, uint32_t v_curr_378_, lean_object* v_next_x3f_379_){
_start:
{
lean_object* v___y_381_; uint8_t v___y_382_; lean_object* v___y_383_; lean_object* v___y_398_; 
if (lean_obj_tag(v_prev_x3f_377_) == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_box(0);
v___y_398_ = v___x_412_;
goto v___jp_397_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_423_; 
v_val_413_ = lean_ctor_get(v_prev_x3f_377_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_prev_x3f_377_);
if (v_isSharedCheck_423_ == 0)
{
v___x_415_ = v_prev_x3f_377_;
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v_prev_x3f_377_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint32_t v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_417_ = lean_unbox_uint32(v_val_413_);
lean_dec(v_val_413_);
v___x_418_ = l_Lean_FuzzyMatching_charType(v___x_417_);
v___x_419_ = lean_box(v___x_418_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_419_);
v___x_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v___y_398_ = v___x_421_;
goto v___jp_397_;
}
}
}
v___jp_380_:
{
if (v___y_382_ == 2)
{
uint8_t v___x_384_; 
lean_dec(v___y_383_);
lean_dec(v___y_381_);
v___x_384_ = 2;
return v___x_384_;
}
else
{
if (lean_obj_tag(v___y_381_) == 0)
{
uint8_t v___x_385_; 
lean_dec(v___y_383_);
v___x_385_ = 0;
return v___x_385_;
}
else
{
lean_object* v_val_386_; uint8_t v___x_387_; 
v_val_386_ = lean_ctor_get(v___y_381_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___y_381_, 1);
v___x_387_ = lean_unbox(v_val_386_);
if (v___x_387_ == 2)
{
uint8_t v___x_388_; 
lean_dec(v_val_386_);
lean_dec(v___y_383_);
v___x_388_ = 0;
return v___x_388_;
}
else
{
if (v___y_382_ == 0)
{
uint8_t v___x_389_; 
lean_dec(v_val_386_);
lean_dec(v___y_383_);
v___x_389_ = 1;
return v___x_389_;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = lean_unbox(v_val_386_);
lean_dec(v_val_386_);
if (v___x_390_ == 1)
{
if (lean_obj_tag(v___y_383_) == 1)
{
lean_object* v_val_391_; uint8_t v___x_392_; 
v_val_391_ = lean_ctor_get(v___y_383_, 0);
lean_inc(v_val_391_);
lean_dec_ref_known(v___y_383_, 1);
v___x_392_ = lean_unbox(v_val_391_);
lean_dec(v_val_391_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 1;
return v___x_394_;
}
}
else
{
uint8_t v___x_395_; 
lean_dec(v___y_383_);
v___x_395_ = 1;
return v___x_395_;
}
}
else
{
uint8_t v___x_396_; 
lean_dec(v___y_383_);
v___x_396_ = 0;
return v___x_396_;
}
}
}
}
}
}
v___jp_397_:
{
uint8_t v___x_399_; 
v___x_399_ = l_Lean_FuzzyMatching_charType(v_curr_378_);
if (lean_obj_tag(v_next_x3f_379_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
v___y_381_ = v___y_398_;
v___y_382_ = v___x_399_;
v___y_383_ = v___x_400_;
goto v___jp_380_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_411_; 
v_val_401_ = lean_ctor_get(v_next_x3f_379_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_next_x3f_379_);
if (v_isSharedCheck_411_ == 0)
{
v___x_403_ = v_next_x3f_379_;
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_val_401_);
lean_dec(v_next_x3f_379_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint32_t v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_405_ = lean_unbox_uint32(v_val_401_);
lean_dec(v_val_401_);
v___x_406_ = l_Lean_FuzzyMatching_charType(v___x_405_);
v___x_407_ = lean_box(v___x_406_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_407_);
v___x_409_ = v___x_403_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
v___y_381_ = v___y_398_;
v___y_382_ = v___x_399_;
v___y_383_ = v___x_409_;
goto v___jp_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* v_prev_x3f_424_, lean_object* v_curr_425_, lean_object* v_next_x3f_426_){
_start:
{
uint32_t v_curr_boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v_curr_boxed_427_ = lean_unbox_uint32(v_curr_425_);
lean_dec(v_curr_425_);
v_res_428_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_424_, v_curr_boxed_427_, v_next_x3f_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* v_string_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_string_utf8_byte_size(v_string_432_);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_nat_dec_eq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_string_length(v_string_432_);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v_result_439_; lean_object* v___x_440_; uint32_t v___x_441_; uint32_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v_result_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint32_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint32_t v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_result_439_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_string_utf8_get(v_string_432_, v___x_434_);
v___x_442_ = lean_string_utf8_get(v_string_432_, v___x_437_);
v___x_443_ = lean_box_uint32(v___x_442_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
v___x_445_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_440_, v___x_441_, v___x_444_);
v___x_446_ = lean_box(v___x_445_);
v_result_447_ = lean_array_push(v_result_439_, v___x_446_);
v___x_448_ = lean_unsigned_to_nat(2u);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_436_);
lean_ctor_set(v___x_449_, 2, v___x_437_);
v___x_450_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_432_, v___x_449_, v_result_447_, v___x_448_);
lean_dec_ref_known(v___x_449_, 3);
v___x_451_ = lean_nat_sub(v___x_436_, v___x_448_);
v___x_452_ = lean_string_utf8_get(v_string_432_, v___x_451_);
lean_dec(v___x_451_);
v___x_453_ = lean_box_uint32(v___x_452_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = lean_nat_sub(v___x_436_, v___x_437_);
v___x_456_ = lean_string_utf8_get(v_string_432_, v___x_455_);
lean_dec(v___x_455_);
v___x_457_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_454_, v___x_456_, v___x_440_);
v___x_458_ = lean_box(v___x_457_);
v___x_459_ = lean_array_push(v___x_450_, v___x_458_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; uint32_t v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_460_ = lean_box(0);
v___x_461_ = lean_string_utf8_get(v_string_432_, v___x_434_);
v___x_462_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_460_, v___x_461_, v___x_460_);
v___x_463_ = lean_mk_empty_array_with_capacity(v___x_437_);
v___x_464_ = lean_box(v___x_462_);
v___x_465_ = lean_array_push(v___x_463_, v___x_464_);
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0));
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* v_string_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_467_);
lean_dec_ref(v_string_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* v_s_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* v_s_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_471_);
lean_dec_ref(v_s_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* v_string_473_, lean_object* v_range_474_, lean_object* v_b_475_, lean_object* v_i_476_, lean_object* v_hs_477_, lean_object* v_hl_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_473_, v_range_474_, v_b_475_, v_i_476_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* v_string_480_, lean_object* v_range_481_, lean_object* v_b_482_, lean_object* v_i_483_, lean_object* v_hs_484_, lean_object* v_hl_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_480_, v_range_481_, v_b_482_, v_i_483_, v_hs_484_, v_hl_485_);
lean_dec(v_i_483_);
lean_dec_ref(v_range_481_);
lean_dec_ref(v_string_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* v_string_487_, lean_object* v_range_488_, lean_object* v_b_489_, lean_object* v_i_490_, lean_object* v_hs_491_, lean_object* v_hl_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_487_, v_range_488_, v_b_489_, v_i_490_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_string_494_, lean_object* v_range_495_, lean_object* v_b_496_, lean_object* v_i_497_, lean_object* v_hs_498_, lean_object* v_hl_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_494_, v_range_495_, v_b_496_, v_i_497_, v_hs_498_, v_hl_499_);
lean_dec_ref(v_range_495_);
lean_dec_ref(v_string_494_);
return v_res_500_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0(void){
_start:
{
lean_object* v___x_501_; uint16_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_int16_of_nat(v___x_501_);
return v___x_502_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default(void){
_start:
{
uint16_t v___x_503_; 
v___x_503_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_503_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore(void){
_start:
{
uint16_t v___x_504_; 
v___x_504_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
return v___x_504_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0(void){
_start:
{
lean_object* v___x_505_; uint16_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(32768u);
v___x_506_ = lean_int16_of_nat(v___x_505_);
return v___x_506_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1(void){
_start:
{
uint16_t v___x_507_; uint16_t v___x_508_; 
v___x_507_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0);
v___x_508_ = lean_int16_neg(v___x_507_);
return v___x_508_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful(void){
_start:
{
uint16_t v___x_509_; 
v___x_509_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
return v___x_509_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t v_x_510_){
_start:
{
uint16_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_512_ = lean_int16_dec_le(v_x_510_, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* v_x_513_){
_start:
{
uint16_t v_x_boxed_514_; uint8_t v_res_515_; lean_object* v_r_516_; 
v_x_boxed_514_ = lean_unbox(v_x_513_);
v_res_515_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_514_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t v_x_517_, lean_object* v_f_518_){
_start:
{
uint16_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_520_ = lean_int16_dec_le(v_x_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; uint16_t v___x_523_; 
v___x_521_ = lean_box(v_x_517_);
v___x_522_ = lean_apply_1(v_f_518_, v___x_521_);
v___x_523_ = lean_unbox(v___x_522_);
return v___x_523_;
}
else
{
lean_dec_ref(v_f_518_);
return v_x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* v_x_524_, lean_object* v_f_525_){
_start:
{
uint16_t v_x_boxed_526_; uint16_t v_res_527_; lean_object* v_r_528_; 
v_x_boxed_526_ = lean_unbox(v_x_524_);
v_res_527_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_boxed_526_, v_f_525_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t v_x_529_){
_start:
{
uint16_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_531_ = lean_int16_dec_le(v_x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(v_x_529_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_box(0);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* v_x_535_){
_start:
{
uint16_t v_x_boxed_536_; lean_object* v_res_537_; 
v_x_boxed_536_ = lean_unbox(v_x_535_);
v_res_537_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_boxed_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t v_x_538_){
_start:
{
uint16_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_540_ = lean_int16_dec_le(v_x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_int16_to_int(v_x_538_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* v_x_544_){
_start:
{
uint16_t v_x_boxed_545_; lean_object* v_res_546_; 
v_x_boxed_545_ = lean_unbox(v_x_544_);
v_res_546_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_545_);
return v_res_546_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = lean_unsigned_to_nat(127u);
v___x_553_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
v___x_554_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
v___x_555_ = l_mkPanicMessageWithDecl(v___x_554_, v___x_553_, v___x_552_, v___x_551_, v___x_550_);
return v___x_555_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t v_x_556_){
_start:
{
uint16_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_558_ = lean_int16_dec_eq(v_x_556_, v___x_557_);
if (v___x_558_ == 0)
{
return v_x_556_;
}
else
{
uint16_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint16_t v___x_563_; 
v___x_559_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_560_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_561_ = lean_box(v___x_559_);
v___x_562_ = l_panic___redArg(v___x_561_, v___x_560_);
lean_dec(v___x_561_);
v___x_563_ = lean_unbox(v___x_562_);
lean_dec(v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* v_x_564_){
_start:
{
uint16_t v_x_boxed_565_; uint16_t v_res_566_; lean_object* v_r_567_; 
v_x_boxed_565_ = lean_unbox(v_x_564_);
v_res_566_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_boxed_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t v_missScore_568_, uint16_t v_matchScore_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_int16_dec_le(v_missScore_568_, v_matchScore_569_);
if (v___x_570_ == 0)
{
return v_missScore_568_;
}
else
{
return v_matchScore_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* v_missScore_571_, lean_object* v_matchScore_572_){
_start:
{
uint16_t v_missScore_boxed_573_; uint16_t v_matchScore_boxed_574_; uint16_t v_res_575_; lean_object* v_r_576_; 
v_missScore_boxed_573_ = lean_unbox(v_missScore_571_);
v_matchScore_boxed_574_ = lean_unbox(v_matchScore_572_);
v_res_575_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_boxed_573_, v_matchScore_boxed_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* v_word_577_, lean_object* v_patternIdx_578_, lean_object* v_wordIdx_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_580_ = lean_string_length(v_word_577_);
v___x_581_ = lean_nat_mul(v_patternIdx_578_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(2u);
v___x_583_ = lean_nat_mul(v___x_581_, v___x_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_nat_mul(v_wordIdx_579_, v___x_582_);
v___x_585_ = lean_nat_add(v___x_583_, v___x_584_);
lean_dec(v___x_584_);
lean_dec(v___x_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* v_word_586_, lean_object* v_patternIdx_587_, lean_object* v_wordIdx_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(v_word_586_, v_patternIdx_587_, v_wordIdx_588_);
lean_dec(v_wordIdx_588_);
lean_dec(v_patternIdx_587_);
lean_dec_ref(v_word_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* v_word_590_, lean_object* v_patternIdx_591_, lean_object* v_wordIdx_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_string_length(v_word_590_);
v___x_594_ = lean_nat_mul(v_patternIdx_591_, v___x_593_);
v___x_595_ = lean_nat_add(v___x_594_, v_wordIdx_592_);
lean_dec(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* v_word_596_, lean_object* v_patternIdx_597_, lean_object* v_wordIdx_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(v_word_596_, v_patternIdx_597_, v_wordIdx_598_);
lean_dec(v_wordIdx_598_);
lean_dec(v_patternIdx_597_);
lean_dec_ref(v_word_596_);
return v_res_599_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* v_word_600_, lean_object* v_result_601_, lean_object* v_patternIdx_602_, lean_object* v_wordIdx_603_){
_start:
{
uint16_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint16_t v___x_613_; 
v___x_604_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_605_ = lean_string_length(v_word_600_);
v___x_606_ = lean_nat_mul(v_patternIdx_602_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(2u);
v___x_608_ = lean_nat_mul(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_nat_mul(v_wordIdx_603_, v___x_607_);
v___x_610_ = lean_nat_add(v___x_608_, v___x_609_);
lean_dec(v___x_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(v___x_604_);
v___x_612_ = lean_array_get(v___x_611_, v_result_601_, v___x_610_);
lean_dec(v___x_610_);
lean_dec(v___x_611_);
v___x_613_ = lean_unbox(v___x_612_);
lean_dec(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* v_word_614_, lean_object* v_result_615_, lean_object* v_patternIdx_616_, lean_object* v_wordIdx_617_){
_start:
{
uint16_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_614_, v_result_615_, v_patternIdx_616_, v_wordIdx_617_);
lean_dec(v_wordIdx_617_);
lean_dec(v_patternIdx_616_);
lean_dec_ref(v_result_615_);
lean_dec_ref(v_word_614_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* v_word_620_, lean_object* v_result_621_, lean_object* v_patternIdx_622_, lean_object* v_wordIdx_623_){
_start:
{
uint16_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint16_t v___x_635_; 
v___x_624_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_625_ = lean_string_length(v_word_620_);
v___x_626_ = lean_nat_mul(v_patternIdx_622_, v___x_625_);
v___x_627_ = lean_unsigned_to_nat(2u);
v___x_628_ = lean_nat_mul(v___x_626_, v___x_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_nat_mul(v_wordIdx_623_, v___x_627_);
v___x_630_ = lean_nat_add(v___x_628_, v___x_629_);
lean_dec(v___x_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(v___x_624_);
v___x_634_ = lean_array_get(v___x_633_, v_result_621_, v___x_632_);
lean_dec(v___x_632_);
lean_dec(v___x_633_);
v___x_635_ = lean_unbox(v___x_634_);
lean_dec(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* v_word_636_, lean_object* v_result_637_, lean_object* v_patternIdx_638_, lean_object* v_wordIdx_639_){
_start:
{
uint16_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_636_, v_result_637_, v_patternIdx_638_, v_wordIdx_639_);
lean_dec(v_wordIdx_639_);
lean_dec(v_patternIdx_638_);
lean_dec_ref(v_result_637_);
lean_dec_ref(v_word_636_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* v_word_642_, lean_object* v_result_643_, lean_object* v_patternIdx_644_, lean_object* v_wordIdx_645_, uint16_t v_missValue_646_, uint16_t v_matchValue_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_idx_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_648_ = lean_string_length(v_word_642_);
v___x_649_ = lean_nat_mul(v_patternIdx_644_, v___x_648_);
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_nat_mul(v___x_649_, v___x_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_nat_mul(v_wordIdx_645_, v___x_650_);
v_idx_653_ = lean_nat_add(v___x_651_, v___x_652_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(v_missValue_646_);
v___x_655_ = lean_array_set(v_result_643_, v_idx_653_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_idx_653_, v___x_656_);
lean_dec(v_idx_653_);
v___x_658_ = lean_box(v_matchValue_647_);
v___x_659_ = lean_array_set(v___x_655_, v___x_657_, v___x_658_);
lean_dec(v___x_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* v_word_660_, lean_object* v_result_661_, lean_object* v_patternIdx_662_, lean_object* v_wordIdx_663_, lean_object* v_missValue_664_, lean_object* v_matchValue_665_){
_start:
{
uint16_t v_missValue_boxed_666_; uint16_t v_matchValue_boxed_667_; lean_object* v_res_668_; 
v_missValue_boxed_666_ = lean_unbox(v_missValue_664_);
v_matchValue_boxed_667_ = lean_unbox(v_matchValue_665_);
v_res_668_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_660_, v_result_661_, v_patternIdx_662_, v_wordIdx_663_, v_missValue_boxed_666_, v_matchValue_boxed_667_);
lean_dec(v_wordIdx_663_);
lean_dec(v_patternIdx_662_);
lean_dec_ref(v_word_660_);
return v_res_668_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0(void){
_start:
{
lean_object* v___x_669_; uint16_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_int16_of_nat(v___x_669_);
return v___x_670_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1(void){
_start:
{
lean_object* v___x_671_; uint16_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(3u);
v___x_672_ = lean_int16_of_nat(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t v_wordRole_673_, uint8_t v_wordStart_674_){
_start:
{
if (v_wordStart_674_ == 0)
{
if (v_wordRole_673_ == 0)
{
uint16_t v___x_675_; 
v___x_675_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
return v___x_675_;
}
else
{
uint16_t v___x_676_; 
v___x_676_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_676_;
}
}
else
{
uint16_t v___x_677_; 
v___x_677_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* v_wordRole_678_, lean_object* v_wordStart_679_){
_start:
{
uint8_t v_wordRole_boxed_680_; uint8_t v_wordStart_boxed_681_; uint16_t v_res_682_; lean_object* v_r_683_; 
v_wordRole_boxed_680_ = lean_unbox(v_wordRole_678_);
v_wordStart_boxed_681_ = lean_unbox(v_wordStart_679_);
v_res_682_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_boxed_680_, v_wordStart_boxed_681_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t v_patternChar_684_, uint32_t v_wordChar_685_, uint8_t v_patternRole_686_, uint8_t v_wordRole_687_){
_start:
{
uint32_t v___y_689_; uint32_t v___y_690_; uint32_t v___y_694_; uint32_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = 65;
v___x_702_ = lean_uint32_dec_le(v___x_701_, v_patternChar_684_);
if (v___x_702_ == 0)
{
v___y_694_ = v_patternChar_684_;
goto v___jp_693_;
}
else
{
uint32_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 90;
v___x_704_ = lean_uint32_dec_le(v_patternChar_684_, v___x_703_);
if (v___x_704_ == 0)
{
v___y_694_ = v_patternChar_684_;
goto v___jp_693_;
}
else
{
uint32_t v___x_705_; uint32_t v___x_706_; 
v___x_705_ = 32;
v___x_706_ = lean_uint32_add(v_patternChar_684_, v___x_705_);
v___y_694_ = v___x_706_;
goto v___jp_693_;
}
}
v___jp_688_:
{
uint8_t v___x_691_; 
v___x_691_ = lean_uint32_dec_eq(v___y_689_, v___y_690_);
if (v___x_691_ == 0)
{
return v___x_691_;
}
else
{
if (v_patternRole_686_ == 0)
{
if (v_wordRole_687_ == 0)
{
return v___x_691_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
}
else
{
return v___x_691_;
}
}
}
v___jp_693_:
{
uint32_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = 65;
v___x_696_ = lean_uint32_dec_le(v___x_695_, v_wordChar_685_);
if (v___x_696_ == 0)
{
v___y_689_ = v___y_694_;
v___y_690_ = v_wordChar_685_;
goto v___jp_688_;
}
else
{
uint32_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 90;
v___x_698_ = lean_uint32_dec_le(v_wordChar_685_, v___x_697_);
if (v___x_698_ == 0)
{
v___y_689_ = v___y_694_;
v___y_690_ = v_wordChar_685_;
goto v___jp_688_;
}
else
{
uint32_t v___x_699_; uint32_t v___x_700_; 
v___x_699_ = 32;
v___x_700_ = lean_uint32_add(v_wordChar_685_, v___x_699_);
v___y_689_ = v___y_694_;
v___y_690_ = v___x_700_;
goto v___jp_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object* v_patternChar_707_, lean_object* v_wordChar_708_, lean_object* v_patternRole_709_, lean_object* v_wordRole_710_){
_start:
{
uint32_t v_patternChar_boxed_711_; uint32_t v_wordChar_boxed_712_; uint8_t v_patternRole_boxed_713_; uint8_t v_wordRole_boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v_patternChar_boxed_711_ = lean_unbox_uint32(v_patternChar_707_);
lean_dec(v_patternChar_707_);
v_wordChar_boxed_712_ = lean_unbox_uint32(v_wordChar_708_);
lean_dec(v_wordChar_708_);
v_patternRole_boxed_713_ = lean_unbox(v_patternRole_709_);
v_wordRole_boxed_714_ = lean_unbox(v_wordRole_710_);
v_res_715_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v_patternChar_boxed_711_, v_wordChar_boxed_712_, v_patternRole_boxed_713_, v_wordRole_boxed_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0(void){
_start:
{
lean_object* v___x_717_; uint16_t v___x_718_; 
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = lean_int16_of_nat(v___x_717_);
return v___x_718_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1(void){
_start:
{
uint16_t v_score_719_; uint16_t v_score_720_; 
v_score_719_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v_score_720_ = lean_int16_add(v_score_719_, v_score_719_);
return v_score_720_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object* v_pattern_721_, lean_object* v_word_722_, lean_object* v_patternIdx_723_, lean_object* v_wordIdx_724_, uint8_t v_patternRole_725_, uint8_t v_wordRole_726_, uint16_t v_consecutive_727_){
_start:
{
uint16_t v_score_729_; uint16_t v_score_734_; lean_object* v___x_739_; uint16_t v_score_741_; uint16_t v_score_750_; uint32_t v___x_753_; uint32_t v___x_754_; uint8_t v___x_755_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v_score_750_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_753_ = lean_string_utf8_get(v_pattern_721_, v_patternIdx_723_);
v___x_754_ = lean_string_utf8_get(v_word_722_, v_wordIdx_724_);
v___x_755_ = lean_uint32_dec_eq(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
if (v_patternRole_725_ == 0)
{
if (v_wordRole_726_ == 0)
{
goto v___jp_751_;
}
else
{
v_score_741_ = v_score_750_;
goto v___jp_740_;
}
}
else
{
v_score_741_ = v_score_750_;
goto v___jp_740_;
}
}
else
{
goto v___jp_751_;
}
v___jp_728_:
{
uint16_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_731_ = lean_int16_dec_le(v_consecutive_727_, v___x_730_);
if (v___x_731_ == 0)
{
uint16_t v_score_732_; 
v_score_732_ = lean_int16_add(v_score_729_, v_consecutive_727_);
return v_score_732_;
}
else
{
return v_score_729_;
}
}
v___jp_733_:
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_nat_dec_eq(v_wordIdx_724_, v___x_735_);
if (v___x_736_ == 0)
{
v_score_729_ = v_score_734_;
goto v___jp_728_;
}
else
{
uint16_t v___x_737_; uint16_t v_score_738_; 
v___x_737_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
v_score_738_ = lean_int16_add(v_score_734_, v___x_737_);
v_score_729_ = v_score_738_;
goto v___jp_728_;
}
}
v___jp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_string_length(v_word_722_);
v___x_743_ = lean_nat_sub(v___x_742_, v___x_739_);
v___x_744_ = lean_nat_dec_eq(v_wordIdx_724_, v___x_743_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
v_score_734_ = v_score_741_;
goto v___jp_733_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_string_length(v_pattern_721_);
v___x_746_ = lean_nat_sub(v___x_745_, v___x_739_);
v___x_747_ = lean_nat_dec_eq(v_patternIdx_723_, v___x_746_);
lean_dec(v___x_746_);
if (v___x_747_ == 0)
{
v_score_734_ = v_score_741_;
goto v___jp_733_;
}
else
{
uint16_t v___x_748_; uint16_t v_score_749_; 
v___x_748_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
v_score_749_ = lean_int16_add(v_score_741_, v___x_748_);
v_score_734_ = v_score_749_;
goto v___jp_733_;
}
}
}
v___jp_751_:
{
uint16_t v_score_752_; 
v_score_752_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
v_score_741_ = v_score_752_;
goto v___jp_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* v_pattern_756_, lean_object* v_word_757_, lean_object* v_patternIdx_758_, lean_object* v_wordIdx_759_, lean_object* v_patternRole_760_, lean_object* v_wordRole_761_, lean_object* v_consecutive_762_){
_start:
{
uint8_t v_patternRole_boxed_763_; uint8_t v_wordRole_boxed_764_; uint16_t v_consecutive_boxed_765_; uint16_t v_res_766_; lean_object* v_r_767_; 
v_patternRole_boxed_763_ = lean_unbox(v_patternRole_760_);
v_wordRole_boxed_764_ = lean_unbox(v_wordRole_761_);
v_consecutive_boxed_765_ = lean_unbox(v_consecutive_762_);
v_res_766_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_756_, v_word_757_, v_patternIdx_758_, v_wordIdx_759_, v_patternRole_boxed_763_, v_wordRole_boxed_764_, v_consecutive_boxed_765_);
lean_dec(v_wordIdx_759_);
lean_dec(v_patternIdx_758_);
lean_dec_ref(v_word_757_);
lean_dec_ref(v_pattern_756_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* v_msg_768_){
_start:
{
uint16_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint16_t v___x_772_; 
v___x_769_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_770_ = lean_box(v___x_769_);
v___x_771_ = lean_panic_fn_borrowed(v___x_770_, v_msg_768_);
lean_dec(v___x_770_);
v___x_772_ = lean_unbox(v___x_771_);
lean_dec(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* v_msg_773_){
_start:
{
uint16_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* v___x_776_, lean_object* v_a_777_, uint16_t v_x_778_){
_start:
{
uint16_t v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_780_ = lean_int16_dec_le(v_x_778_, v___x_779_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; 
v___x_781_ = lean_nat_dec_le(v___x_776_, v_a_777_);
if (v___x_781_ == 0)
{
return v_x_778_;
}
else
{
uint16_t v___x_782_; uint16_t v___x_783_; 
v___x_782_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_783_ = lean_int16_add(v_x_778_, v___x_782_);
return v___x_783_;
}
}
else
{
return v_x_778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* v___x_784_, lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
uint16_t v_x_boxed_787_; uint16_t v_res_788_; lean_object* v_r_789_; 
v_x_boxed_787_ = lean_unbox(v_x_786_);
v_res_788_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_784_, v_a_785_, v_x_boxed_787_);
lean_dec(v_a_785_);
lean_dec(v___x_784_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* v_pattern_790_, lean_object* v_word_791_, lean_object* v_a_792_, lean_object* v_a_793_, uint8_t v___x_794_, uint8_t v___x_795_, lean_object* v___x_796_, uint16_t v_x_797_){
_start:
{
uint16_t v_matchScore_798_; uint8_t v___x_799_; 
v_matchScore_798_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_799_ = lean_int16_dec_le(v_x_797_, v_matchScore_798_);
if (v___x_799_ == 0)
{
uint16_t v___x_800_; uint16_t v___x_801_; uint16_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint16_t v___x_805_; uint16_t v___x_806_; 
v___x_800_ = l_instInhabitedInt16;
v___x_801_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_790_, v_word_791_, v_a_792_, v_a_793_, v___x_794_, v___x_795_, v_matchScore_798_);
v___x_802_ = lean_int16_add(v_x_797_, v___x_801_);
v___x_803_ = lean_box(v___x_800_);
v___x_804_ = lean_array_get(v___x_803_, v___x_796_, v_a_793_);
lean_dec(v___x_803_);
v___x_805_ = lean_unbox(v___x_804_);
lean_dec(v___x_804_);
v___x_806_ = lean_int16_sub(v___x_802_, v___x_805_);
return v___x_806_;
}
else
{
return v_x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* v_pattern_807_, lean_object* v_word_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v___x_813_, lean_object* v_x_814_){
_start:
{
uint8_t v___x_3022__boxed_815_; uint8_t v___x_3023__boxed_816_; uint16_t v_x_boxed_817_; uint16_t v_res_818_; lean_object* v_r_819_; 
v___x_3022__boxed_815_ = lean_unbox(v___x_811_);
v___x_3023__boxed_816_ = lean_unbox(v___x_812_);
v_x_boxed_817_ = lean_unbox(v_x_814_);
v_res_818_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_807_, v_word_808_, v_a_809_, v_a_810_, v___x_3022__boxed_815_, v___x_3023__boxed_816_, v___x_813_, v_x_boxed_817_);
lean_dec_ref(v___x_813_);
lean_dec(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_word_808_);
lean_dec_ref(v_pattern_807_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* v_pattern_820_, lean_object* v_word_821_, lean_object* v_a_822_, lean_object* v_a_823_, uint8_t v___x_824_, uint8_t v___x_825_, uint16_t v___x_826_, uint16_t v_x_827_){
_start:
{
uint16_t v___y_829_; uint16_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_833_ = lean_int16_dec_le(v_x_827_, v___x_832_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; 
v___x_834_ = lean_int16_dec_eq(v___x_826_, v___x_832_);
if (v___x_834_ == 0)
{
v___y_829_ = v___x_826_;
goto v___jp_828_;
}
else
{
lean_object* v___x_835_; uint16_t v___x_836_; 
v___x_835_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_836_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_835_);
v___y_829_ = v___x_836_;
goto v___jp_828_;
}
}
else
{
return v_x_827_;
}
v___jp_828_:
{
uint16_t v___x_830_; uint16_t v___x_831_; 
v___x_830_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_820_, v_word_821_, v_a_822_, v_a_823_, v___x_824_, v___x_825_, v___y_829_);
v___x_831_ = lean_int16_add(v_x_827_, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* v_pattern_837_, lean_object* v_word_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v___x_841_, lean_object* v___x_842_, lean_object* v___x_843_, lean_object* v_x_844_){
_start:
{
uint8_t v___x_3062__boxed_845_; uint8_t v___x_3063__boxed_846_; uint16_t v___x_3064__boxed_847_; uint16_t v_x_boxed_848_; uint16_t v_res_849_; lean_object* v_r_850_; 
v___x_3062__boxed_845_ = lean_unbox(v___x_841_);
v___x_3063__boxed_846_ = lean_unbox(v___x_842_);
v___x_3064__boxed_847_ = lean_unbox(v___x_843_);
v_x_boxed_848_ = lean_unbox(v_x_844_);
v_res_849_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_837_, v_word_838_, v_a_839_, v_a_840_, v___x_3062__boxed_845_, v___x_3063__boxed_846_, v___x_3064__boxed_847_, v_x_boxed_848_);
lean_dec(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_word_838_);
lean_dec_ref(v_pattern_837_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* v_word_851_, lean_object* v_a_852_, lean_object* v_pattern_853_, lean_object* v_patternRoles_854_, lean_object* v_wordRoles_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_range_858_, lean_object* v_b_859_, lean_object* v_i_860_){
_start:
{
lean_object* v_stop_861_; lean_object* v_step_862_; uint8_t v___x_863_; 
v_stop_861_ = lean_ctor_get(v_range_858_, 1);
v_step_862_ = lean_ctor_get(v_range_858_, 2);
v___x_863_ = lean_nat_dec_lt(v_i_860_, v_stop_861_);
if (v___x_863_ == 0)
{
lean_dec(v_i_860_);
return v_b_859_;
}
else
{
lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_978_; 
v_fst_864_ = lean_ctor_get(v_b_859_, 0);
v_snd_865_ = lean_ctor_get(v_b_859_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_b_859_);
if (v_isSharedCheck_978_ == 0)
{
v___x_867_ = v_b_859_;
v_isShared_868_ = v_isSharedCheck_978_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v_b_859_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_978_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; uint16_t v_matchScore_870_; uint16_t v___x_871_; lean_object* v___x_872_; uint16_t v___y_874_; lean_object* v_runLengths_875_; uint16_t v_matchScore_876_; uint16_t v___y_894_; lean_object* v___y_895_; uint16_t v___y_896_; uint16_t v___y_899_; uint8_t v___x_959_; 
v___x_869_ = 0;
v_matchScore_870_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_871_ = l_instInhabitedInt16;
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_dec_le(v___x_872_, v_i_860_);
if (v___x_959_ == 0)
{
v___y_899_ = v_matchScore_870_;
goto v___jp_898_;
}
else
{
lean_object* v___x_960_; uint16_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint16_t v___x_973_; uint16_t v___x_974_; uint8_t v___x_975_; 
v___x_960_ = lean_nat_sub(v_i_860_, v___x_872_);
v___x_961_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_962_ = lean_string_length(v_word_851_);
v___x_963_ = lean_nat_mul(v_a_852_, v___x_962_);
v___x_964_ = lean_unsigned_to_nat(2u);
v___x_965_ = lean_nat_mul(v___x_963_, v___x_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_nat_mul(v___x_960_, v___x_964_);
lean_dec(v___x_960_);
v___x_967_ = lean_nat_add(v___x_965_, v___x_966_);
lean_dec(v___x_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(v___x_961_);
v___x_969_ = lean_array_get(v___x_968_, v_fst_864_, v___x_967_);
lean_dec(v___x_968_);
v___x_970_ = lean_nat_add(v___x_967_, v___x_872_);
lean_dec(v___x_967_);
v___x_971_ = lean_box(v___x_961_);
v___x_972_ = lean_array_get(v___x_971_, v_fst_864_, v___x_970_);
lean_dec(v___x_970_);
lean_dec(v___x_971_);
v___x_973_ = lean_unbox(v___x_969_);
v___x_974_ = lean_unbox(v___x_972_);
v___x_975_ = lean_int16_dec_le(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
uint16_t v___x_976_; 
lean_dec(v___x_972_);
v___x_976_ = lean_unbox(v___x_969_);
lean_dec(v___x_969_);
v___y_899_ = v___x_976_;
goto v___jp_898_;
}
else
{
uint16_t v___x_977_; 
lean_dec(v___x_969_);
v___x_977_ = lean_unbox(v___x_972_);
lean_dec(v___x_972_);
v___y_899_ = v___x_977_;
goto v___jp_898_;
}
}
v___jp_873_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_idx_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_877_ = lean_string_length(v_word_851_);
v___x_878_ = lean_nat_mul(v_a_852_, v___x_877_);
v___x_879_ = lean_unsigned_to_nat(2u);
v___x_880_ = lean_nat_mul(v___x_878_, v___x_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_nat_mul(v_i_860_, v___x_879_);
v_idx_882_ = lean_nat_add(v___x_880_, v___x_881_);
lean_dec(v___x_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(v___y_874_);
v___x_884_ = lean_array_set(v_fst_864_, v_idx_882_, v___x_883_);
v___x_885_ = lean_nat_add(v_idx_882_, v___x_872_);
lean_dec(v_idx_882_);
v___x_886_ = lean_box(v_matchScore_876_);
v___x_887_ = lean_array_set(v___x_884_, v___x_885_, v___x_886_);
lean_dec(v___x_885_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v_runLengths_875_);
lean_ctor_set(v___x_867_, 0, v___x_887_);
v___x_889_ = v___x_867_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_runLengths_875_);
v___x_889_ = v_reuseFailAlloc_892_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; 
v___x_890_ = lean_nat_add(v_i_860_, v_step_862_);
lean_dec(v_i_860_);
v_b_859_ = v___x_889_;
v_i_860_ = v___x_890_;
goto _start;
}
}
v___jp_893_:
{
uint16_t v___x_897_; 
v___x_897_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_857_, v_i_860_, v___y_896_);
v___y_874_ = v___y_894_;
v_runLengths_875_ = v___y_895_;
v_matchScore_876_ = v___x_897_;
goto v___jp_873_;
}
v___jp_898_:
{
uint32_t v___x_900_; uint32_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; 
v___x_900_ = lean_string_utf8_get(v_pattern_853_, v_a_852_);
v___x_901_ = lean_string_utf8_get(v_word_851_, v_i_860_);
v___x_902_ = lean_box(v___x_869_);
v___x_903_ = lean_array_get(v___x_902_, v_patternRoles_854_, v_a_852_);
lean_dec(v___x_902_);
v___x_904_ = lean_box(v___x_869_);
v___x_905_ = lean_array_get(v___x_904_, v_wordRoles_855_, v_i_860_);
lean_dec(v___x_904_);
v___x_906_ = lean_unbox(v___x_903_);
v___x_907_ = lean_unbox(v___x_905_);
v___x_908_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_900_, v___x_901_, v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v___x_905_);
lean_dec(v___x_903_);
v___y_874_ = v___y_899_;
v_runLengths_875_ = v_snd_865_;
v_matchScore_876_ = v_matchScore_870_;
goto v___jp_873_;
}
else
{
uint8_t v___x_909_; 
v___x_909_ = lean_nat_dec_le(v___x_872_, v_a_852_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint16_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; uint8_t v___x_917_; uint16_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint16_t v___x_921_; uint16_t v___x_922_; uint8_t v___x_923_; 
v___x_910_ = lean_string_length(v_word_851_);
v___x_911_ = lean_nat_mul(v_a_852_, v___x_910_);
v___x_912_ = lean_nat_add(v___x_911_, v_i_860_);
lean_dec(v___x_911_);
v___x_913_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_914_ = lean_box(v___x_913_);
v___x_915_ = lean_array_set(v_snd_865_, v___x_912_, v___x_914_);
lean_dec(v___x_912_);
v___x_916_ = lean_unbox(v___x_903_);
lean_dec(v___x_903_);
v___x_917_ = lean_unbox(v___x_905_);
lean_dec(v___x_905_);
v___x_918_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_853_, v_word_851_, v_a_852_, v_i_860_, v___x_916_, v___x_917_, v_matchScore_870_);
v___x_919_ = lean_box(v___x_871_);
v___x_920_ = lean_array_get(v___x_919_, v___x_856_, v_i_860_);
lean_dec(v___x_919_);
v___x_921_ = lean_unbox(v___x_920_);
lean_dec(v___x_920_);
v___x_922_ = lean_int16_sub(v___x_918_, v___x_921_);
v___x_923_ = lean_int16_dec_eq(v___x_922_, v_matchScore_870_);
if (v___x_923_ == 0)
{
v___y_874_ = v___y_899_;
v_runLengths_875_ = v___x_915_;
v_matchScore_876_ = v___x_922_;
goto v___jp_873_;
}
else
{
lean_object* v___x_924_; uint16_t v___x_925_; 
v___x_924_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_925_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_924_);
v___y_874_ = v___y_899_;
v_runLengths_875_ = v___x_915_;
v_matchScore_876_ = v___x_925_;
goto v___jp_873_;
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint16_t v___x_933_; uint16_t v___x_934_; uint16_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint16_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; uint16_t v___x_949_; uint16_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; uint8_t v___x_955_; uint16_t v___x_956_; uint16_t v___x_957_; uint8_t v___x_958_; 
v___x_926_ = lean_nat_sub(v_a_852_, v___x_872_);
v___x_927_ = lean_nat_sub(v_i_860_, v___x_872_);
v___x_928_ = lean_string_length(v_word_851_);
v___x_929_ = lean_nat_mul(v___x_926_, v___x_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_nat_add(v___x_929_, v___x_927_);
v___x_931_ = lean_box(v___x_871_);
v___x_932_ = lean_array_get(v___x_931_, v_snd_865_, v___x_930_);
lean_dec(v___x_930_);
lean_dec(v___x_931_);
v___x_933_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_934_ = lean_unbox(v___x_932_);
lean_dec(v___x_932_);
v___x_935_ = lean_int16_add(v___x_934_, v___x_933_);
v___x_936_ = lean_nat_mul(v_a_852_, v___x_928_);
v___x_937_ = lean_nat_add(v___x_936_, v_i_860_);
lean_dec(v___x_936_);
v___x_938_ = lean_box(v___x_935_);
v___x_939_ = lean_array_set(v_snd_865_, v___x_937_, v___x_938_);
lean_dec(v___x_937_);
v___x_940_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_941_ = lean_unsigned_to_nat(2u);
v___x_942_ = lean_nat_mul(v___x_929_, v___x_941_);
lean_dec(v___x_929_);
v___x_943_ = lean_nat_mul(v___x_927_, v___x_941_);
lean_dec(v___x_927_);
v___x_944_ = lean_nat_add(v___x_942_, v___x_943_);
lean_dec(v___x_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(v___x_940_);
v___x_946_ = lean_array_get(v___x_945_, v_fst_864_, v___x_944_);
lean_dec(v___x_945_);
v___x_947_ = lean_unbox(v___x_903_);
v___x_948_ = lean_unbox(v___x_905_);
v___x_949_ = lean_unbox(v___x_946_);
lean_dec(v___x_946_);
v___x_950_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_853_, v_word_851_, v_a_852_, v_i_860_, v___x_947_, v___x_948_, v___x_856_, v___x_949_);
v___x_951_ = lean_nat_add(v___x_944_, v___x_872_);
lean_dec(v___x_944_);
v___x_952_ = lean_box(v___x_940_);
v___x_953_ = lean_array_get(v___x_952_, v_fst_864_, v___x_951_);
lean_dec(v___x_951_);
lean_dec(v___x_952_);
v___x_954_ = lean_unbox(v___x_903_);
lean_dec(v___x_903_);
v___x_955_ = lean_unbox(v___x_905_);
lean_dec(v___x_905_);
v___x_956_ = lean_unbox(v___x_953_);
lean_dec(v___x_953_);
v___x_957_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_853_, v_word_851_, v_a_852_, v_i_860_, v___x_954_, v___x_955_, v___x_935_, v___x_956_);
v___x_958_ = lean_int16_dec_le(v___x_950_, v___x_957_);
if (v___x_958_ == 0)
{
v___y_894_ = v___y_899_;
v___y_895_ = v___x_939_;
v___y_896_ = v___x_950_;
goto v___jp_893_;
}
else
{
v___y_894_ = v___y_899_;
v___y_895_ = v___x_939_;
v___y_896_ = v___x_957_;
goto v___jp_893_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* v_word_979_, lean_object* v_a_980_, lean_object* v_pattern_981_, lean_object* v_patternRoles_982_, lean_object* v_wordRoles_983_, lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v_range_986_, lean_object* v_b_987_, lean_object* v_i_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_979_, v_a_980_, v_pattern_981_, v_patternRoles_982_, v_wordRoles_983_, v___x_984_, v___x_985_, v_range_986_, v_b_987_, v_i_988_);
lean_dec_ref(v_range_986_);
lean_dec(v___x_985_);
lean_dec_ref(v___x_984_);
lean_dec_ref(v_wordRoles_983_);
lean_dec_ref(v_patternRoles_982_);
lean_dec_ref(v_pattern_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_word_979_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object* v___x_990_, lean_object* v___x_991_, lean_object* v_word_992_, lean_object* v_pattern_993_, lean_object* v_patternRoles_994_, lean_object* v_wordRoles_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_range_998_, lean_object* v_b_999_, lean_object* v_i_1000_){
_start:
{
lean_object* v_stop_1001_; lean_object* v_step_1002_; uint8_t v___x_1003_; 
v_stop_1001_ = lean_ctor_get(v_range_998_, 1);
v_step_1002_ = lean_ctor_get(v_range_998_, 2);
v___x_1003_ = lean_nat_dec_lt(v_i_1000_, v_stop_1001_);
if (v___x_1003_ == 0)
{
lean_dec(v_i_1000_);
return v_b_999_;
}
else
{
lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1029_; 
v_fst_1004_ = lean_ctor_get(v_b_999_, 0);
v_snd_1005_ = lean_ctor_get(v_b_999_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_b_999_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1007_ = v_b_999_;
v_isShared_1008_ = v_isSharedCheck_1029_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_snd_1005_);
lean_inc(v_fst_1004_);
lean_dec(v_b_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1029_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_sub(v___x_990_, v_i_1000_);
v___x_1011_ = lean_nat_sub(v___x_1010_, v___x_1009_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_nat_sub(v___x_991_, v___x_1011_);
lean_dec(v___x_1011_);
lean_inc(v_i_1000_);
v___x_1013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1013_, 0, v_i_1000_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_ctor_set(v___x_1013_, 2, v___x_1009_);
if (v_isShared_1008_ == 0)
{
v___x_1015_ = v___x_1007_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_fst_1004_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_snd_1005_);
v___x_1015_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1027_; 
lean_inc(v_i_1000_);
v___x_1016_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_992_, v_i_1000_, v_pattern_993_, v_patternRoles_994_, v_wordRoles_995_, v___x_996_, v___x_997_, v___x_1013_, v___x_1015_, v_i_1000_);
lean_dec_ref_known(v___x_1013_, 3);
v_fst_1017_ = lean_ctor_get(v___x_1016_, 0);
v_snd_1018_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1020_ = v___x_1016_;
v_isShared_1021_ = v_isSharedCheck_1027_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_inc(v_fst_1017_);
lean_dec(v___x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1027_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_fst_1017_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_snd_1018_);
v___x_1023_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_nat_add(v_i_1000_, v_step_1002_);
lean_dec(v_i_1000_);
v_b_999_ = v___x_1023_;
v_i_1000_ = v___x_1024_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v_word_1032_, lean_object* v_pattern_1033_, lean_object* v_patternRoles_1034_, lean_object* v_wordRoles_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_range_1038_, lean_object* v_b_1039_, lean_object* v_i_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1030_, v___x_1031_, v_word_1032_, v_pattern_1033_, v_patternRoles_1034_, v_wordRoles_1035_, v___x_1036_, v___x_1037_, v_range_1038_, v_b_1039_, v_i_1040_);
lean_dec_ref(v_range_1038_);
lean_dec(v___x_1037_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_wordRoles_1035_);
lean_dec_ref(v_patternRoles_1034_);
lean_dec_ref(v_pattern_1033_);
lean_dec_ref(v_word_1032_);
lean_dec(v___x_1031_);
lean_dec(v___x_1030_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* v_word_1042_, lean_object* v_pattern_1043_, lean_object* v_patternRoles_1044_, lean_object* v_wordRoles_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v___x_1049_, lean_object* v_range_1050_, lean_object* v_b_1051_, lean_object* v_i_1052_){
_start:
{
lean_object* v_stop_1053_; lean_object* v_step_1054_; uint8_t v___x_1055_; 
v_stop_1053_ = lean_ctor_get(v_range_1050_, 1);
v_step_1054_ = lean_ctor_get(v_range_1050_, 2);
v___x_1055_ = lean_nat_dec_lt(v_i_1052_, v_stop_1053_);
if (v___x_1055_ == 0)
{
lean_dec(v_i_1052_);
return v_b_1051_;
}
else
{
lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1081_; 
v_fst_1056_ = lean_ctor_get(v_b_1051_, 0);
v_snd_1057_ = lean_ctor_get(v_b_1051_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_b_1051_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1059_ = v_b_1051_;
v_isShared_1060_ = v_isSharedCheck_1081_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snd_1057_);
lean_inc(v_fst_1056_);
lean_dec(v_b_1051_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1081_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_sub(v___x_1048_, v_i_1052_);
v___x_1063_ = lean_nat_sub(v___x_1062_, v___x_1061_);
lean_dec(v___x_1062_);
v___x_1064_ = lean_nat_sub(v___x_1049_, v___x_1063_);
lean_dec(v___x_1063_);
lean_inc(v_i_1052_);
v___x_1065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1065_, 0, v_i_1052_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
lean_ctor_set(v___x_1065_, 2, v___x_1061_);
if (v_isShared_1060_ == 0)
{
v___x_1067_ = v___x_1059_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_snd_1057_);
v___x_1067_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1079_; 
lean_inc(v_i_1052_);
v___x_1068_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1042_, v_i_1052_, v_pattern_1043_, v_patternRoles_1044_, v_wordRoles_1045_, v___x_1046_, v___x_1047_, v___x_1065_, v___x_1067_, v_i_1052_);
lean_dec_ref_known(v___x_1065_, 3);
v_fst_1069_ = lean_ctor_get(v___x_1068_, 0);
v_snd_1070_ = lean_ctor_get(v___x_1068_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1072_ = v___x_1068_;
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_snd_1070_);
lean_inc(v_fst_1069_);
lean_dec(v___x_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1079_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fst_1069_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_snd_1070_);
v___x_1075_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_nat_add(v_i_1052_, v_step_1054_);
lean_dec(v_i_1052_);
v___x_1077_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1048_, v___x_1049_, v_word_1042_, v_pattern_1043_, v_patternRoles_1044_, v_wordRoles_1045_, v___x_1046_, v___x_1047_, v_range_1050_, v___x_1075_, v___x_1076_);
return v___x_1077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* v_word_1082_, lean_object* v_pattern_1083_, lean_object* v_patternRoles_1084_, lean_object* v_wordRoles_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_range_1090_, lean_object* v_b_1091_, lean_object* v_i_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1082_, v_pattern_1083_, v_patternRoles_1084_, v_wordRoles_1085_, v___x_1086_, v___x_1087_, v___x_1088_, v___x_1089_, v_range_1090_, v_b_1091_, v_i_1092_);
lean_dec_ref(v_range_1090_);
lean_dec(v___x_1089_);
lean_dec(v___x_1088_);
lean_dec(v___x_1087_);
lean_dec_ref(v___x_1086_);
lean_dec_ref(v_wordRoles_1085_);
lean_dec_ref(v_patternRoles_1084_);
lean_dec_ref(v_pattern_1083_);
lean_dec_ref(v_word_1082_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* v_wordRoles_1094_, lean_object* v_range_1095_, lean_object* v_b_1096_, lean_object* v_i_1097_){
_start:
{
lean_object* v_stop_1098_; lean_object* v_step_1099_; uint8_t v___x_1100_; 
v_stop_1098_ = lean_ctor_get(v_range_1095_, 1);
v_step_1099_ = lean_ctor_get(v_range_1095_, 2);
v___x_1100_ = lean_nat_dec_lt(v_i_1097_, v_stop_1098_);
if (v___x_1100_ == 0)
{
lean_dec(v_i_1097_);
return v_b_1096_;
}
else
{
lean_object* v_snd_1101_; lean_object* v_snd_1102_; lean_object* v_fst_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1159_; 
v_snd_1101_ = lean_ctor_get(v_b_1096_, 1);
lean_inc(v_snd_1101_);
v_snd_1102_ = lean_ctor_get(v_snd_1101_, 1);
lean_inc(v_snd_1102_);
v_fst_1103_ = lean_ctor_get(v_b_1096_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_b_1096_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_b_1096_, 1);
lean_dec(v_unused_1160_);
v___x_1105_ = v_b_1096_;
v_isShared_1106_ = v_isSharedCheck_1159_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_fst_1103_);
lean_dec(v_b_1096_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1159_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_fst_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1157_; 
v_fst_1107_ = lean_ctor_get(v_snd_1101_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_snd_1101_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_snd_1101_, 1);
lean_dec(v_unused_1158_);
v___x_1109_ = v_snd_1101_;
v_isShared_1110_ = v_isSharedCheck_1157_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_fst_1107_);
lean_dec(v_snd_1101_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1157_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1156_; 
v_fst_1111_ = lean_ctor_get(v_snd_1102_, 0);
v_snd_1112_ = lean_ctor_get(v_snd_1102_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_snd_1102_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1114_ = v_snd_1102_;
v_isShared_1115_ = v_isSharedCheck_1156_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v_snd_1102_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1156_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint8_t v___x_1116_; lean_object* v_lastSepIdx_1117_; lean_object* v_lastSepIdx_1119_; uint16_t v_penaltyNs_1120_; uint16_t v_penaltySkip_1121_; uint8_t v___x_1144_; 
v___x_1116_ = 0;
v_lastSepIdx_1117_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_nat_dec_eq(v_i_1097_, v_lastSepIdx_1117_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_box(v___x_1116_);
v___x_1146_ = lean_array_get(v___x_1145_, v_wordRoles_1094_, v_i_1097_);
lean_dec(v___x_1145_);
v___x_1147_ = lean_unbox(v___x_1146_);
lean_dec(v___x_1146_);
if (v___x_1147_ == 2)
{
uint16_t v_penaltyNs_1148_; uint16_t v___x_1149_; uint16_t v___x_1150_; uint16_t v___x_1151_; 
lean_dec(v_snd_1112_);
lean_dec(v_fst_1107_);
v_penaltyNs_1148_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1149_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1150_ = lean_unbox(v_fst_1111_);
lean_dec(v_fst_1111_);
v___x_1151_ = lean_int16_add(v___x_1150_, v___x_1149_);
lean_inc(v_i_1097_);
v_lastSepIdx_1119_ = v_i_1097_;
v_penaltyNs_1120_ = v___x_1151_;
v_penaltySkip_1121_ = v_penaltyNs_1148_;
goto v___jp_1118_;
}
else
{
uint16_t v___x_1152_; uint16_t v___x_1153_; 
v___x_1152_ = lean_unbox(v_fst_1111_);
lean_dec(v_fst_1111_);
v___x_1153_ = lean_unbox(v_snd_1112_);
lean_dec(v_snd_1112_);
v_lastSepIdx_1119_ = v_fst_1107_;
v_penaltyNs_1120_ = v___x_1152_;
v_penaltySkip_1121_ = v___x_1153_;
goto v___jp_1118_;
}
}
else
{
uint16_t v___x_1154_; uint16_t v___x_1155_; 
v___x_1154_ = lean_unbox(v_fst_1111_);
lean_dec(v_fst_1111_);
v___x_1155_ = lean_unbox(v_snd_1112_);
lean_dec(v_snd_1112_);
v_lastSepIdx_1119_ = v_fst_1107_;
v_penaltyNs_1120_ = v___x_1154_;
v_penaltySkip_1121_ = v___x_1155_;
goto v___jp_1118_;
}
v___jp_1118_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; uint8_t v___x_1125_; uint16_t v___x_1126_; uint16_t v___x_1127_; uint16_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1122_ = lean_box(v___x_1116_);
v___x_1123_ = lean_array_get(v___x_1122_, v_wordRoles_1094_, v_i_1097_);
lean_dec(v___x_1122_);
v___x_1124_ = lean_nat_dec_eq(v_i_1097_, v_lastSepIdx_1117_);
v___x_1125_ = lean_unbox(v___x_1123_);
lean_dec(v___x_1123_);
v___x_1126_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_1125_, v___x_1124_);
v___x_1127_ = lean_int16_add(v_penaltySkip_1121_, v___x_1126_);
v___x_1128_ = lean_int16_add(v___x_1127_, v_penaltyNs_1120_);
v___x_1129_ = lean_box(v___x_1128_);
v___x_1130_ = lean_array_set(v_fst_1103_, v_i_1097_, v___x_1129_);
v___x_1131_ = lean_box(v_penaltyNs_1120_);
v___x_1132_ = lean_box(v___x_1127_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1132_);
lean_ctor_set(v___x_1114_, 0, v___x_1131_);
v___x_1134_ = v___x_1114_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1134_);
lean_ctor_set(v___x_1109_, 0, v_lastSepIdx_1119_);
v___x_1136_ = v___x_1109_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_lastSepIdx_1119_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v___x_1136_);
lean_ctor_set(v___x_1105_, 0, v___x_1130_);
v___x_1138_ = v___x_1105_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_nat_add(v_i_1097_, v_step_1099_);
lean_dec(v_i_1097_);
v_b_1096_ = v___x_1138_;
v_i_1097_ = v___x_1139_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* v_wordRoles_1161_, lean_object* v_range_1162_, lean_object* v_b_1163_, lean_object* v_i_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1161_, v_range_1162_, v_b_1163_, v_i_1164_);
lean_dec_ref(v_range_1162_);
lean_dec_ref(v_wordRoles_1161_);
return v_res_1165_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0(void){
_start:
{
uint16_t v_penaltyNs_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_penaltyNs_1166_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1167_ = lean_box(v_penaltyNs_1166_);
v___x_1168_ = lean_box(v_penaltyNs_1166_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v_lastSepIdx_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
v_lastSepIdx_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_lastSepIdx_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* v_pattern_1173_, lean_object* v_word_1174_, lean_object* v_patternRoles_1175_, lean_object* v_wordRoles_1176_){
_start:
{
uint16_t v___y_1178_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_lastSepIdx_1189_; uint16_t v_penaltyNs_1190_; lean_object* v___x_1191_; lean_object* v_runLengths_1192_; lean_object* v___x_1193_; lean_object* v_startPenalties_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_snd_1200_; lean_object* v_fst_1201_; lean_object* v_fst_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1232_; 
v___x_1184_ = lean_string_length(v_pattern_1173_);
v___x_1185_ = lean_string_length(v_word_1174_);
v___x_1186_ = lean_nat_mul(v___x_1184_, v___x_1185_);
v___x_1187_ = lean_unsigned_to_nat(2u);
v___x_1188_ = lean_nat_mul(v___x_1186_, v___x_1187_);
v_lastSepIdx_1189_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1190_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1191_ = lean_box(v_penaltyNs_1190_);
v_runLengths_1192_ = lean_mk_array(v___x_1186_, v___x_1191_);
v___x_1193_ = lean_box(v_penaltyNs_1190_);
v_startPenalties_1194_ = lean_mk_array(v___x_1185_, v___x_1193_);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1196_, 0, v_lastSepIdx_1189_);
lean_ctor_set(v___x_1196_, 1, v___x_1185_);
lean_ctor_set(v___x_1196_, 2, v___x_1195_);
v___x_1197_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_startPenalties_1194_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1176_, v___x_1196_, v___x_1198_, v_lastSepIdx_1189_);
lean_dec_ref_known(v___x_1196_, 3);
v_snd_1200_ = lean_ctor_get(v___x_1199_, 1);
lean_inc(v_snd_1200_);
v_fst_1201_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_fst_1201_);
lean_dec_ref(v___x_1199_);
v_fst_1202_ = lean_ctor_get(v_snd_1200_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_snd_1200_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_snd_1200_, 1);
lean_dec(v_unused_1233_);
v___x_1204_ = v_snd_1200_;
v_isShared_1205_ = v_isSharedCheck_1232_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_fst_1202_);
lean_dec(v_snd_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1232_;
goto v_resetjp_1203_;
}
v___jp_1177_:
{
uint16_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1180_ = lean_int16_dec_le(v___y_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_int16_to_int(v___y_1178_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
}
v_resetjp_1203_:
{
uint16_t v_matchScore_1206_; lean_object* v___x_1207_; lean_object* v_result_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v_matchScore_1206_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1207_ = lean_box(v_matchScore_1206_);
v_result_1208_ = lean_mk_array(v___x_1188_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1209_, 0, v_lastSepIdx_1189_);
lean_ctor_set(v___x_1209_, 1, v___x_1184_);
lean_ctor_set(v___x_1209_, 2, v___x_1195_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_runLengths_1192_);
lean_ctor_set(v___x_1204_, 0, v_result_1208_);
v___x_1211_ = v___x_1204_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_result_1208_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_runLengths_1192_);
v___x_1211_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v_fst_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint16_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint16_t v___x_1226_; uint16_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1212_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1174_, v_pattern_1173_, v_patternRoles_1175_, v_wordRoles_1176_, v_fst_1201_, v_fst_1202_, v___x_1184_, v___x_1185_, v___x_1209_, v___x_1211_, v_lastSepIdx_1189_);
lean_dec_ref_known(v___x_1209_, 3);
lean_dec(v_fst_1202_);
lean_dec(v_fst_1201_);
v_fst_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_fst_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_nat_sub(v___x_1184_, v___x_1195_);
v___x_1215_ = lean_nat_sub(v___x_1185_, v___x_1195_);
v___x_1216_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1217_ = lean_nat_mul(v___x_1214_, v___x_1185_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_nat_mul(v___x_1217_, v___x_1187_);
lean_dec(v___x_1217_);
v___x_1219_ = lean_nat_mul(v___x_1215_, v___x_1187_);
lean_dec(v___x_1215_);
v___x_1220_ = lean_nat_add(v___x_1218_, v___x_1219_);
lean_dec(v___x_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(v___x_1216_);
v___x_1222_ = lean_array_get(v___x_1221_, v_fst_1213_, v___x_1220_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_nat_add(v___x_1220_, v___x_1195_);
lean_dec(v___x_1220_);
v___x_1224_ = lean_box(v___x_1216_);
v___x_1225_ = lean_array_get(v___x_1224_, v_fst_1213_, v___x_1223_);
lean_dec(v___x_1223_);
lean_dec(v_fst_1213_);
lean_dec(v___x_1224_);
v___x_1226_ = lean_unbox(v___x_1222_);
v___x_1227_ = lean_unbox(v___x_1225_);
v___x_1228_ = lean_int16_dec_le(v___x_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint16_t v___x_1229_; 
lean_dec(v___x_1225_);
v___x_1229_ = lean_unbox(v___x_1222_);
lean_dec(v___x_1222_);
v___y_1178_ = v___x_1229_;
goto v___jp_1177_;
}
else
{
uint16_t v___x_1230_; 
lean_dec(v___x_1222_);
v___x_1230_ = lean_unbox(v___x_1225_);
lean_dec(v___x_1225_);
v___y_1178_ = v___x_1230_;
goto v___jp_1177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* v_pattern_1234_, lean_object* v_word_1235_, lean_object* v_patternRoles_1236_, lean_object* v_wordRoles_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1234_, v_word_1235_, v_patternRoles_1236_, v_wordRoles_1237_);
lean_dec_ref(v_wordRoles_1237_);
lean_dec_ref(v_patternRoles_1236_);
lean_dec_ref(v_word_1235_);
lean_dec_ref(v_pattern_1234_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* v_wordRoles_1239_, lean_object* v_range_1240_, lean_object* v_b_1241_, lean_object* v_i_1242_, lean_object* v_hs_1243_, lean_object* v_hl_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1239_, v_range_1240_, v_b_1241_, v_i_1242_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* v_wordRoles_1246_, lean_object* v_range_1247_, lean_object* v_b_1248_, lean_object* v_i_1249_, lean_object* v_hs_1250_, lean_object* v_hl_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_1246_, v_range_1247_, v_b_1248_, v_i_1249_, v_hs_1250_, v_hl_1251_);
lean_dec_ref(v_range_1247_);
lean_dec_ref(v_wordRoles_1246_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* v_word_1253_, lean_object* v_a_1254_, lean_object* v_pattern_1255_, lean_object* v_patternRoles_1256_, lean_object* v_wordRoles_1257_, lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v_range_1260_, lean_object* v_b_1261_, lean_object* v_i_1262_, lean_object* v_hs_1263_, lean_object* v_hl_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1253_, v_a_1254_, v_pattern_1255_, v_patternRoles_1256_, v_wordRoles_1257_, v___x_1258_, v___x_1259_, v_range_1260_, v_b_1261_, v_i_1262_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* v_word_1266_, lean_object* v_a_1267_, lean_object* v_pattern_1268_, lean_object* v_patternRoles_1269_, lean_object* v_wordRoles_1270_, lean_object* v___x_1271_, lean_object* v___x_1272_, lean_object* v_range_1273_, lean_object* v_b_1274_, lean_object* v_i_1275_, lean_object* v_hs_1276_, lean_object* v_hl_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v_word_1266_, v_a_1267_, v_pattern_1268_, v_patternRoles_1269_, v_wordRoles_1270_, v___x_1271_, v___x_1272_, v_range_1273_, v_b_1274_, v_i_1275_, v_hs_1276_, v_hl_1277_);
lean_dec_ref(v_range_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v___x_1271_);
lean_dec_ref(v_wordRoles_1270_);
lean_dec_ref(v_patternRoles_1269_);
lean_dec_ref(v_pattern_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_word_1266_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* v_word_1279_, lean_object* v_pattern_1280_, lean_object* v_patternRoles_1281_, lean_object* v_wordRoles_1282_, lean_object* v___x_1283_, lean_object* v___x_1284_, lean_object* v___x_1285_, lean_object* v___x_1286_, lean_object* v_range_1287_, lean_object* v_b_1288_, lean_object* v_i_1289_, lean_object* v_hs_1290_, lean_object* v_hl_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1279_, v_pattern_1280_, v_patternRoles_1281_, v_wordRoles_1282_, v___x_1283_, v___x_1284_, v___x_1285_, v___x_1286_, v_range_1287_, v_b_1288_, v_i_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* v_word_1293_, lean_object* v_pattern_1294_, lean_object* v_patternRoles_1295_, lean_object* v_wordRoles_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v___x_1299_, lean_object* v___x_1300_, lean_object* v_range_1301_, lean_object* v_b_1302_, lean_object* v_i_1303_, lean_object* v_hs_1304_, lean_object* v_hl_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v_word_1293_, v_pattern_1294_, v_patternRoles_1295_, v_wordRoles_1296_, v___x_1297_, v___x_1298_, v___x_1299_, v___x_1300_, v_range_1301_, v_b_1302_, v_i_1303_, v_hs_1304_, v_hl_1305_);
lean_dec_ref(v_range_1301_);
lean_dec(v___x_1300_);
lean_dec(v___x_1299_);
lean_dec(v___x_1298_);
lean_dec_ref(v___x_1297_);
lean_dec_ref(v_wordRoles_1296_);
lean_dec_ref(v_patternRoles_1295_);
lean_dec_ref(v_pattern_1294_);
lean_dec_ref(v_word_1293_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v_word_1309_, lean_object* v_pattern_1310_, lean_object* v_patternRoles_1311_, lean_object* v_wordRoles_1312_, lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v_range_1315_, lean_object* v_b_1316_, lean_object* v_i_1317_, lean_object* v_hs_1318_, lean_object* v_hl_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1307_, v___x_1308_, v_word_1309_, v_pattern_1310_, v_patternRoles_1311_, v_wordRoles_1312_, v___x_1313_, v___x_1314_, v_range_1315_, v_b_1316_, v_i_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_word_1323_, lean_object* v_pattern_1324_, lean_object* v_patternRoles_1325_, lean_object* v_wordRoles_1326_, lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_range_1329_, lean_object* v_b_1330_, lean_object* v_i_1331_, lean_object* v_hs_1332_, lean_object* v_hl_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(v___x_1321_, v___x_1322_, v_word_1323_, v_pattern_1324_, v_patternRoles_1325_, v_wordRoles_1326_, v___x_1327_, v___x_1328_, v_range_1329_, v_b_1330_, v_i_1331_, v_hs_1332_, v_hl_1333_);
lean_dec_ref(v_range_1329_);
lean_dec(v___x_1328_);
lean_dec_ref(v___x_1327_);
lean_dec_ref(v_wordRoles_1326_);
lean_dec_ref(v_patternRoles_1325_);
lean_dec_ref(v_pattern_1324_);
lean_dec_ref(v_word_1323_);
lean_dec(v___x_1322_);
lean_dec(v___x_1321_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_nat_to_int(v_a_1335_);
return v___x_1336_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1337_; double v___x_1338_; 
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_float_of_nat(v___x_1337_);
return v___x_1338_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1(void){
_start:
{
lean_object* v___x_1339_; double v___x_1340_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_float_of_nat(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_unsigned_to_nat(2u);
v___x_1342_ = lean_nat_to_int(v___x_1341_);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1(void){
_start:
{
double v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1344_ = lean_box_float(v___x_1343_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* v_pattern_1347_, lean_object* v_word_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = lean_string_utf8_byte_size(v_pattern_1347_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_nat_dec_eq(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_score_1355_; uint8_t v___x_1374_; 
v___x_1352_ = lean_string_length(v_word_1348_);
v___x_1353_ = lean_string_length(v_pattern_1347_);
v___x_1374_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Lean_String_charactersIn(v_pattern_1347_, v_word_1348_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_1347_);
v___x_1378_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_1348_);
v___x_1379_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1347_, v_word_1348_, v___x_1377_, v___x_1378_);
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___x_1377_);
if (lean_obj_tag(v___x_1379_) == 1)
{
lean_object* v_val_1380_; uint8_t v___x_1381_; 
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = lean_nat_dec_eq(v___x_1353_, v___x_1352_);
if (v___x_1381_ == 0)
{
v_score_1355_ = v_val_1380_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1382_; lean_object* v_score_1383_; 
v___x_1382_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
v_score_1383_ = lean_int_mul(v_val_1380_, v___x_1382_);
lean_dec(v_val_1380_);
v_score_1355_ = v_score_1383_;
goto v___jp_1354_;
}
}
else
{
lean_object* v___x_1384_; 
lean_dec(v___x_1379_);
v___x_1384_ = lean_box(0);
return v___x_1384_;
}
}
}
else
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_box(0);
return v___x_1385_;
}
v___jp_1354_:
{
lean_object* v_perfect_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_perfectMatch_1363_; double v___x_1364_; lean_object* v___x_1365_; double v___x_1366_; double v_normScore_1367_; double v___x_1368_; double v___x_1369_; double v___x_1370_; double v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_perfect_1356_ = lean_unsigned_to_nat(4u);
v___x_1357_ = lean_nat_mul(v_perfect_1356_, v___x_1353_);
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v___x_1353_, v___x_1358_);
v___x_1360_ = lean_nat_mul(v___x_1353_, v___x_1359_);
lean_dec(v___x_1359_);
v___x_1361_ = lean_nat_shiftr(v___x_1360_, v___x_1358_);
lean_dec(v___x_1360_);
v___x_1362_ = lean_nat_sub(v___x_1361_, v___x_1358_);
lean_dec(v___x_1361_);
v_perfectMatch_1363_ = lean_nat_add(v___x_1357_, v___x_1362_);
lean_dec(v___x_1362_);
lean_dec(v___x_1357_);
v___x_1364_ = l_Float_ofInt(v_score_1355_);
lean_dec(v_score_1355_);
v___x_1365_ = lean_nat_to_int(v_perfectMatch_1363_);
v___x_1366_ = l_Float_ofInt(v___x_1365_);
lean_dec(v___x_1365_);
v_normScore_1367_ = lean_float_div(v___x_1364_, v___x_1366_);
v___x_1368_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1369_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1);
v___x_1370_ = lean_float_maximum(v___x_1369_, v_normScore_1367_);
v___x_1371_ = lean_float_minimum(v___x_1368_, v___x_1370_);
v___x_1372_ = lean_box_float(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
else
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* v_pattern_1387_, lean_object* v_word_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1387_, v_word_1388_);
lean_dec_ref(v_word_1388_);
lean_dec_ref(v_pattern_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* v_pattern_1390_, lean_object* v_word_1391_, double v_threshold_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1390_, v_word_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
return v___x_1393_;
}
else
{
lean_object* v_val_1394_; double v___x_1395_; uint8_t v___x_1396_; 
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
v___x_1395_ = lean_unbox_float(v_val_1394_);
v___x_1396_ = lean_float_decLt(v_threshold_1392_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v___x_1393_, 1);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
else
{
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* v_pattern_1398_, lean_object* v_word_1399_, lean_object* v_threshold_1400_){
_start:
{
double v_threshold_boxed_1401_; lean_object* v_res_1402_; 
v_threshold_boxed_1401_ = lean_unbox_float(v_threshold_1400_);
lean_dec_ref(v_threshold_1400_);
v_res_1402_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1398_, v_word_1399_, v_threshold_boxed_1401_);
lean_dec_ref(v_word_1399_);
lean_dec_ref(v_pattern_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* v_pattern_1403_, lean_object* v_word_1404_, double v_threshold_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1403_, v_word_1404_, v_threshold_1405_);
if (lean_obj_tag(v___x_1406_) == 0)
{
uint8_t v___x_1407_; 
v___x_1407_ = 0;
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = 1;
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* v_pattern_1409_, lean_object* v_word_1410_, lean_object* v_threshold_1411_){
_start:
{
double v_threshold_boxed_1412_; uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_threshold_boxed_1412_ = lean_unbox_float(v_threshold_1411_);
lean_dec_ref(v_threshold_1411_);
v_res_1413_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1409_, v_word_1410_, v_threshold_boxed_1412_);
lean_dec_ref(v_word_1410_);
lean_dec_ref(v_pattern_1409_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
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
