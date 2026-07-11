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
uint8_t lean_bool_not(uint8_t);
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
static lean_once_cell_t l_Lean_FuzzyMatching_charRole___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_FuzzyMatching_charRole___closed__0;
static lean_once_cell_t l_Lean_FuzzyMatching_charRole___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_FuzzyMatching_charRole___closed__1;
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(uint8_t, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint8_t _init_l_Lean_FuzzyMatching_charRole___closed__0(void){
_start:
{
uint8_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 1;
v___x_302_ = lean_bool_not(v___x_301_);
return v___x_302_;
}
}
static uint8_t _init_l_Lean_FuzzyMatching_charRole___closed__1(void){
_start:
{
uint8_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 0;
v___x_304_ = lean_bool_not(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_charRole(lean_object* v_prev_x3f_305_, uint8_t v_curr_306_, lean_object* v_next_x3f_307_){
_start:
{
uint8_t v___y_309_; 
if (v_curr_306_ == 2)
{
uint8_t v___x_312_; 
v___x_312_ = 2;
return v___x_312_;
}
else
{
if (lean_obj_tag(v_prev_x3f_305_) == 0)
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
else
{
lean_object* v_val_314_; uint8_t v___x_315_; 
v_val_314_ = lean_ctor_get(v_prev_x3f_305_, 0);
v___x_315_ = lean_unbox(v_val_314_);
if (v___x_315_ == 2)
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
else
{
if (v_curr_306_ == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 1;
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_unbox(v_val_314_);
if (v___x_318_ == 1)
{
if (lean_obj_tag(v_next_x3f_307_) == 1)
{
lean_object* v_val_319_; uint8_t v___x_320_; 
v_val_319_ = lean_ctor_get(v_next_x3f_307_, 0);
v___x_320_ = lean_unbox(v_val_319_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = lean_uint8_once(&l_Lean_FuzzyMatching_charRole___closed__0, &l_Lean_FuzzyMatching_charRole___closed__0_once, _init_l_Lean_FuzzyMatching_charRole___closed__0);
v___y_309_ = v___x_321_;
goto v___jp_308_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = lean_uint8_once(&l_Lean_FuzzyMatching_charRole___closed__1, &l_Lean_FuzzyMatching_charRole___closed__1_once, _init_l_Lean_FuzzyMatching_charRole___closed__1);
v___y_309_ = v___x_322_;
goto v___jp_308_;
}
}
else
{
uint8_t v___x_323_; 
v___x_323_ = lean_uint8_once(&l_Lean_FuzzyMatching_charRole___closed__1, &l_Lean_FuzzyMatching_charRole___closed__1_once, _init_l_Lean_FuzzyMatching_charRole___closed__1);
v___y_309_ = v___x_323_;
goto v___jp_308_;
}
}
else
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
}
}
}
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = 1;
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_charRole___boxed(lean_object* v_prev_x3f_325_, lean_object* v_curr_326_, lean_object* v_next_x3f_327_){
_start:
{
uint8_t v_curr_boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_curr_boxed_328_ = lean_unbox(v_curr_326_);
v_res_329_ = l_Lean_FuzzyMatching_charRole(v_prev_x3f_325_, v_curr_boxed_328_, v_next_x3f_327_);
lean_dec(v_next_x3f_327_);
lean_dec(v_prev_x3f_325_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_string_331_, lean_object* v_range_332_, lean_object* v_b_333_, lean_object* v_i_334_){
_start:
{
lean_object* v_stop_335_; lean_object* v_step_336_; uint8_t v___y_338_; uint8_t v___y_344_; uint8_t v___x_347_; 
v_stop_335_ = lean_ctor_get(v_range_332_, 1);
v_step_336_ = lean_ctor_get(v_range_332_, 2);
v___x_347_ = lean_nat_dec_lt(v_i_334_, v_stop_335_);
if (v___x_347_ == 0)
{
lean_dec(v_i_334_);
return v_b_333_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; uint32_t v___x_350_; uint8_t v___x_351_; 
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_sub(v_i_334_, v___x_348_);
v___x_350_ = lean_string_utf8_get(v_string_331_, v___x_349_);
lean_dec(v___x_349_);
v___x_351_ = l_Lean_FuzzyMatching_charType(v___x_350_);
if (v___x_351_ == 2)
{
uint8_t v___x_352_; 
v___x_352_ = 2;
v___y_338_ = v___x_352_;
goto v___jp_337_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(2u);
v___x_354_ = lean_nat_sub(v_i_334_, v___x_353_);
v___x_355_ = lean_string_utf8_get(v_string_331_, v___x_354_);
lean_dec(v___x_354_);
v___x_356_ = l_Lean_FuzzyMatching_charType(v___x_355_);
if (v___x_356_ == 2)
{
uint8_t v___x_357_; 
v___x_357_ = 0;
v___y_338_ = v___x_357_;
goto v___jp_337_;
}
else
{
if (v___x_351_ == 0)
{
uint8_t v___x_358_; 
v___x_358_ = 1;
v___y_338_ = v___x_358_;
goto v___jp_337_;
}
else
{
if (v___x_356_ == 1)
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_string_utf8_get(v_string_331_, v_i_334_);
v___x_360_ = l_Lean_FuzzyMatching_charType(v___x_359_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
v___x_361_ = lean_bool_not(v___x_347_);
v___y_344_ = v___x_361_;
goto v___jp_343_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = lean_uint8_once(&l_Lean_FuzzyMatching_charRole___closed__1, &l_Lean_FuzzyMatching_charRole___closed__1_once, _init_l_Lean_FuzzyMatching_charRole___closed__1);
v___y_344_ = v___x_362_;
goto v___jp_343_;
}
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
v___y_338_ = v___x_363_;
goto v___jp_337_;
}
}
}
}
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_box(v___y_338_);
v___x_340_ = lean_array_push(v_b_333_, v___x_339_);
v___x_341_ = lean_nat_add(v_i_334_, v_step_336_);
lean_dec(v_i_334_);
v_b_333_ = v___x_340_;
v_i_334_ = v___x_341_;
goto _start;
}
v___jp_343_:
{
if (v___y_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 0;
v___y_338_ = v___x_345_;
goto v___jp_337_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 1;
v___y_338_ = v___x_346_;
goto v___jp_337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_string_364_, lean_object* v_range_365_, lean_object* v_b_366_, lean_object* v_i_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_364_, v_range_365_, v_b_366_, v_i_367_);
lean_dec_ref(v_range_365_);
lean_dec_ref(v_string_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(lean_object* v_string_369_, lean_object* v_range_370_, lean_object* v_b_371_, lean_object* v_i_372_){
_start:
{
lean_object* v_stop_373_; lean_object* v_step_374_; uint8_t v___y_376_; uint8_t v___y_382_; uint8_t v___x_385_; 
v_stop_373_ = lean_ctor_get(v_range_370_, 1);
v_step_374_ = lean_ctor_get(v_range_370_, 2);
v___x_385_ = lean_nat_dec_lt(v_i_372_, v_stop_373_);
if (v___x_385_ == 0)
{
return v_b_371_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_sub(v_i_372_, v___x_386_);
v___x_388_ = lean_string_utf8_get(v_string_369_, v___x_387_);
lean_dec(v___x_387_);
v___x_389_ = l_Lean_FuzzyMatching_charType(v___x_388_);
if (v___x_389_ == 2)
{
uint8_t v___x_390_; 
v___x_390_ = 2;
v___y_376_ = v___x_390_;
goto v___jp_375_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(2u);
v___x_392_ = lean_nat_sub(v_i_372_, v___x_391_);
v___x_393_ = lean_string_utf8_get(v_string_369_, v___x_392_);
lean_dec(v___x_392_);
v___x_394_ = l_Lean_FuzzyMatching_charType(v___x_393_);
if (v___x_394_ == 2)
{
uint8_t v___x_395_; 
v___x_395_ = 0;
v___y_376_ = v___x_395_;
goto v___jp_375_;
}
else
{
if (v___x_389_ == 0)
{
uint8_t v___x_396_; 
v___x_396_ = 1;
v___y_376_ = v___x_396_;
goto v___jp_375_;
}
else
{
if (v___x_394_ == 1)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_string_utf8_get(v_string_369_, v_i_372_);
v___x_398_ = l_Lean_FuzzyMatching_charType(v___x_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
v___x_399_ = lean_bool_not(v___x_385_);
v___y_382_ = v___x_399_;
goto v___jp_381_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_uint8_once(&l_Lean_FuzzyMatching_charRole___closed__1, &l_Lean_FuzzyMatching_charRole___closed__1_once, _init_l_Lean_FuzzyMatching_charRole___closed__1);
v___y_382_ = v___x_400_;
goto v___jp_381_;
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
v___y_376_ = v___x_401_;
goto v___jp_375_;
}
}
}
}
}
v___jp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_box(v___y_376_);
v___x_378_ = lean_array_push(v_b_371_, v___x_377_);
v___x_379_ = lean_nat_add(v_i_372_, v_step_374_);
v___x_380_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_369_, v_range_370_, v___x_378_, v___x_379_);
return v___x_380_;
}
v___jp_381_:
{
if (v___y_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = 0;
v___y_376_ = v___x_383_;
goto v___jp_375_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 1;
v___y_376_ = v___x_384_;
goto v___jp_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(lean_object* v_string_402_, lean_object* v_range_403_, lean_object* v_b_404_, lean_object* v_i_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_402_, v_range_403_, v_b_404_, v_i_405_);
lean_dec(v_i_405_);
lean_dec_ref(v_range_403_);
lean_dec_ref(v_string_402_);
return v_res_406_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(uint8_t v___x_407_, lean_object* v_prev_x3f_408_, uint32_t v_curr_409_, lean_object* v_next_x3f_410_){
_start:
{
uint8_t v___y_412_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_433_; 
if (lean_obj_tag(v_prev_x3f_408_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_box(0);
v___y_433_ = v___x_447_;
goto v___jp_432_;
}
else
{
lean_object* v_val_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_458_; 
v_val_448_ = lean_ctor_get(v_prev_x3f_408_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_prev_x3f_408_);
if (v_isSharedCheck_458_ == 0)
{
v___x_450_ = v_prev_x3f_408_;
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_val_448_);
lean_dec(v_prev_x3f_408_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint32_t v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_452_ = lean_unbox_uint32(v_val_448_);
lean_dec(v_val_448_);
v___x_453_ = l_Lean_FuzzyMatching_charType(v___x_452_);
v___x_454_ = lean_box(v___x_453_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_454_);
v___x_456_ = v___x_450_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v___y_433_ = v___x_456_;
goto v___jp_432_;
}
}
}
v___jp_411_:
{
if (v___y_412_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
}
v___jp_415_:
{
if (v___y_416_ == 2)
{
uint8_t v___x_419_; 
lean_dec(v___y_418_);
lean_dec(v___y_417_);
v___x_419_ = 2;
return v___x_419_;
}
else
{
if (lean_obj_tag(v___y_417_) == 0)
{
uint8_t v___x_420_; 
lean_dec(v___y_418_);
v___x_420_ = 0;
return v___x_420_;
}
else
{
lean_object* v_val_421_; uint8_t v___x_422_; 
v_val_421_ = lean_ctor_get(v___y_417_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v___y_417_, 1);
v___x_422_ = lean_unbox(v_val_421_);
if (v___x_422_ == 2)
{
uint8_t v___x_423_; 
lean_dec(v_val_421_);
lean_dec(v___y_418_);
v___x_423_ = 0;
return v___x_423_;
}
else
{
if (v___y_416_ == 0)
{
uint8_t v___x_424_; 
lean_dec(v_val_421_);
lean_dec(v___y_418_);
v___x_424_ = 1;
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = lean_unbox(v_val_421_);
lean_dec(v_val_421_);
if (v___x_425_ == 1)
{
if (lean_obj_tag(v___y_418_) == 1)
{
lean_object* v_val_426_; uint8_t v___x_427_; 
v_val_426_ = lean_ctor_get(v___y_418_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v___y_418_, 1);
v___x_427_ = lean_unbox(v_val_426_);
lean_dec(v_val_426_);
if (v___x_427_ == 0)
{
uint8_t v___x_428_; 
v___x_428_ = lean_uint8_once(&l_Lean_FuzzyMatching_charRole___closed__0, &l_Lean_FuzzyMatching_charRole___closed__0_once, _init_l_Lean_FuzzyMatching_charRole___closed__0);
v___y_412_ = v___x_428_;
goto v___jp_411_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = lean_bool_not(v___x_407_);
v___y_412_ = v___x_429_;
goto v___jp_411_;
}
}
else
{
uint8_t v___x_430_; 
lean_dec(v___y_418_);
v___x_430_ = lean_bool_not(v___x_407_);
v___y_412_ = v___x_430_;
goto v___jp_411_;
}
}
else
{
uint8_t v___x_431_; 
lean_dec(v___y_418_);
v___x_431_ = 0;
return v___x_431_;
}
}
}
}
}
}
v___jp_432_:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_FuzzyMatching_charType(v_curr_409_);
if (lean_obj_tag(v_next_x3f_410_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
v___y_416_ = v___x_434_;
v___y_417_ = v___y_433_;
v___y_418_ = v___x_435_;
goto v___jp_415_;
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_val_436_ = lean_ctor_get(v_next_x3f_410_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_next_x3f_410_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_next_x3f_410_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v_next_x3f_410_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint32_t v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_440_ = lean_unbox_uint32(v_val_436_);
lean_dec(v_val_436_);
v___x_441_ = l_Lean_FuzzyMatching_charType(v___x_440_);
v___x_442_ = lean_box(v___x_441_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_442_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v___y_416_ = v___x_434_;
v___y_417_ = v___y_433_;
v___y_418_ = v___x_444_;
goto v___jp_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(lean_object* v___x_459_, lean_object* v_prev_x3f_460_, lean_object* v_curr_461_, lean_object* v_next_x3f_462_){
_start:
{
uint8_t v___x_860__boxed_463_; uint32_t v_curr_boxed_464_; uint8_t v_res_465_; lean_object* v_r_466_; 
v___x_860__boxed_463_ = lean_unbox(v___x_459_);
v_curr_boxed_464_ = lean_unbox_uint32(v_curr_461_);
lean_dec(v_curr_461_);
v_res_465_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_860__boxed_463_, v_prev_x3f_460_, v_curr_boxed_464_, v_next_x3f_462_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(lean_object* v_string_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_string_utf8_byte_size(v_string_469_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_nat_dec_eq(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_string_length(v_string_469_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v_result_476_; lean_object* v___x_477_; uint32_t v___x_478_; uint32_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v_result_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint32_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint32_t v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_result_476_ = lean_mk_empty_array_with_capacity(v___x_473_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_string_utf8_get(v_string_469_, v___x_471_);
v___x_479_ = lean_string_utf8_get(v_string_469_, v___x_474_);
v___x_480_ = lean_box_uint32(v___x_479_);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
v___x_482_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_472_, v___x_477_, v___x_478_, v___x_481_);
v___x_483_ = lean_box(v___x_482_);
v_result_484_ = lean_array_push(v_result_476_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_473_);
lean_ctor_set(v___x_486_, 2, v___x_474_);
v___x_487_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_469_, v___x_486_, v_result_484_, v___x_485_);
lean_dec_ref_known(v___x_486_, 3);
v___x_488_ = lean_nat_sub(v___x_473_, v___x_485_);
v___x_489_ = lean_string_utf8_get(v_string_469_, v___x_488_);
lean_dec(v___x_488_);
v___x_490_ = lean_box_uint32(v___x_489_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
v___x_492_ = lean_nat_sub(v___x_473_, v___x_474_);
v___x_493_ = lean_string_utf8_get(v_string_469_, v___x_492_);
lean_dec(v___x_492_);
v___x_494_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_472_, v___x_491_, v___x_493_, v___x_477_);
v___x_495_ = lean_box(v___x_494_);
v___x_496_ = lean_array_push(v___x_487_, v___x_495_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; uint32_t v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_497_ = lean_box(0);
v___x_498_ = lean_string_utf8_get(v_string_469_, v___x_471_);
v___x_499_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_472_, v___x_497_, v___x_498_, v___x_497_);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_501_ = lean_box(v___x_499_);
v___x_502_ = lean_array_push(v___x_500_, v___x_501_);
return v___x_502_;
}
}
else
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0));
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(lean_object* v_string_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_504_);
lean_dec_ref(v_string_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(lean_object* v_s_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(lean_object* v_s_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_508_);
lean_dec_ref(v_s_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(lean_object* v_string_510_, lean_object* v_range_511_, lean_object* v_b_512_, lean_object* v_i_513_, lean_object* v_hs_514_, lean_object* v_hl_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_510_, v_range_511_, v_b_512_, v_i_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(lean_object* v_string_517_, lean_object* v_range_518_, lean_object* v_b_519_, lean_object* v_i_520_, lean_object* v_hs_521_, lean_object* v_hl_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_517_, v_range_518_, v_b_519_, v_i_520_, v_hs_521_, v_hl_522_);
lean_dec(v_i_520_);
lean_dec_ref(v_range_518_);
lean_dec_ref(v_string_517_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(lean_object* v_string_524_, lean_object* v_range_525_, lean_object* v_b_526_, lean_object* v_i_527_, lean_object* v_hs_528_, lean_object* v_hl_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_524_, v_range_525_, v_b_526_, v_i_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_string_531_, lean_object* v_range_532_, lean_object* v_b_533_, lean_object* v_i_534_, lean_object* v_hs_535_, lean_object* v_hl_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_531_, v_range_532_, v_b_533_, v_i_534_, v_hs_535_, v_hl_536_);
lean_dec_ref(v_range_532_);
lean_dec_ref(v_string_531_);
return v_res_537_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0(void){
_start:
{
lean_object* v___x_538_; uint16_t v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_int16_of_nat(v___x_538_);
return v___x_539_;
}
}
static uint16_t _init_l_Lean_FuzzyMatching_instInhabitedScore_default(void){
_start:
{
uint16_t v___x_540_; 
v___x_540_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_540_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore(void){
_start:
{
uint16_t v___x_541_; 
v___x_541_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
return v___x_541_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0(void){
_start:
{
lean_object* v___x_542_; uint16_t v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(32768u);
v___x_543_ = lean_int16_of_nat(v___x_542_);
return v___x_543_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1(void){
_start:
{
uint16_t v___x_544_; uint16_t v___x_545_; 
v___x_544_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0);
v___x_545_ = lean_int16_neg(v___x_544_);
return v___x_545_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful(void){
_start:
{
uint16_t v___x_546_; 
v___x_546_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
return v___x_546_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(uint16_t v_x_547_){
_start:
{
uint16_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_549_ = lean_int16_dec_le(v_x_547_, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(lean_object* v_x_550_){
_start:
{
uint16_t v_x_boxed_551_; uint8_t v_res_552_; lean_object* v_r_553_; 
v_x_boxed_551_ = lean_unbox(v_x_550_);
v_res_552_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_551_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(uint16_t v_x_554_, lean_object* v_f_555_){
_start:
{
uint16_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_557_ = lean_int16_dec_le(v_x_554_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; uint16_t v___x_560_; 
v___x_558_ = lean_box(v_x_554_);
v___x_559_ = lean_apply_1(v_f_555_, v___x_558_);
v___x_560_ = lean_unbox(v___x_559_);
return v___x_560_;
}
else
{
lean_dec_ref(v_f_555_);
return v_x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(lean_object* v_x_561_, lean_object* v_f_562_){
_start:
{
uint16_t v_x_boxed_563_; uint16_t v_res_564_; lean_object* v_r_565_; 
v_x_boxed_563_ = lean_unbox(v_x_561_);
v_res_564_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(v_x_boxed_563_, v_f_562_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(uint16_t v_x_566_){
_start:
{
uint16_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_568_ = lean_int16_dec_le(v_x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_box(v_x_566_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(lean_object* v_x_572_){
_start:
{
uint16_t v_x_boxed_573_; lean_object* v_res_574_; 
v_x_boxed_573_ = lean_unbox(v_x_572_);
v_res_574_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(v_x_boxed_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(uint16_t v_x_575_){
_start:
{
uint16_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_577_ = lean_int16_dec_le(v_x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_int16_to_int(v_x_575_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(lean_object* v_x_581_){
_start:
{
uint16_t v_x_boxed_582_; lean_object* v_res_583_; 
v_x_boxed_582_ = lean_unbox(v_x_581_);
v_res_583_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_582_);
return v_res_583_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2));
v___x_588_ = lean_unsigned_to_nat(2u);
v___x_589_ = lean_unsigned_to_nat(124u);
v___x_590_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1));
v___x_591_ = ((lean_object*)(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0));
v___x_592_ = l_mkPanicMessageWithDecl(v___x_591_, v___x_590_, v___x_589_, v___x_588_, v___x_587_);
return v___x_592_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(uint16_t v_x_593_){
_start:
{
uint16_t v___x_594_; uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_595_ = lean_int16_dec_eq(v_x_593_, v___x_594_);
v___x_596_ = lean_bool_not(v___x_595_);
if (v___x_596_ == 0)
{
uint16_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint16_t v___x_601_; 
v___x_597_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_598_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_599_ = lean_box(v___x_597_);
v___x_600_ = l_panic___redArg(v___x_599_, v___x_598_);
lean_dec(v___x_599_);
v___x_601_ = lean_unbox(v___x_600_);
lean_dec(v___x_600_);
return v___x_601_;
}
else
{
return v_x_593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(lean_object* v_x_602_){
_start:
{
uint16_t v_x_boxed_603_; uint16_t v_res_604_; lean_object* v_r_605_; 
v_x_boxed_603_ = lean_unbox(v_x_602_);
v_res_604_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(v_x_boxed_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(uint16_t v_missScore_606_, uint16_t v_matchScore_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_int16_dec_le(v_missScore_606_, v_matchScore_607_);
if (v___x_608_ == 0)
{
return v_missScore_606_;
}
else
{
return v_matchScore_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(lean_object* v_missScore_609_, lean_object* v_matchScore_610_){
_start:
{
uint16_t v_missScore_boxed_611_; uint16_t v_matchScore_boxed_612_; uint16_t v_res_613_; lean_object* v_r_614_; 
v_missScore_boxed_611_ = lean_unbox(v_missScore_609_);
v_matchScore_boxed_612_ = lean_unbox(v_matchScore_610_);
v_res_613_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(v_missScore_boxed_611_, v_matchScore_boxed_612_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(lean_object* v_word_615_, lean_object* v_patternIdx_616_, lean_object* v_wordIdx_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_618_ = lean_string_length(v_word_615_);
v___x_619_ = lean_nat_mul(v_patternIdx_616_, v___x_618_);
v___x_620_ = lean_unsigned_to_nat(2u);
v___x_621_ = lean_nat_mul(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_nat_mul(v_wordIdx_617_, v___x_620_);
v___x_623_ = lean_nat_add(v___x_621_, v___x_622_);
lean_dec(v___x_622_);
lean_dec(v___x_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(lean_object* v_word_624_, lean_object* v_patternIdx_625_, lean_object* v_wordIdx_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(v_word_624_, v_patternIdx_625_, v_wordIdx_626_);
lean_dec(v_wordIdx_626_);
lean_dec(v_patternIdx_625_);
lean_dec_ref(v_word_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(lean_object* v_word_628_, lean_object* v_patternIdx_629_, lean_object* v_wordIdx_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_string_length(v_word_628_);
v___x_632_ = lean_nat_mul(v_patternIdx_629_, v___x_631_);
v___x_633_ = lean_nat_add(v___x_632_, v_wordIdx_630_);
lean_dec(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(lean_object* v_word_634_, lean_object* v_patternIdx_635_, lean_object* v_wordIdx_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(v_word_634_, v_patternIdx_635_, v_wordIdx_636_);
lean_dec(v_wordIdx_636_);
lean_dec(v_patternIdx_635_);
lean_dec_ref(v_word_634_);
return v_res_637_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(lean_object* v_word_638_, lean_object* v_result_639_, lean_object* v_patternIdx_640_, lean_object* v_wordIdx_641_){
_start:
{
uint16_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint16_t v___x_651_; 
v___x_642_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_643_ = lean_string_length(v_word_638_);
v___x_644_ = lean_nat_mul(v_patternIdx_640_, v___x_643_);
v___x_645_ = lean_unsigned_to_nat(2u);
v___x_646_ = lean_nat_mul(v___x_644_, v___x_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_nat_mul(v_wordIdx_641_, v___x_645_);
v___x_648_ = lean_nat_add(v___x_646_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(v___x_642_);
v___x_650_ = lean_array_get(v___x_649_, v_result_639_, v___x_648_);
lean_dec(v___x_648_);
lean_dec(v___x_649_);
v___x_651_ = lean_unbox(v___x_650_);
lean_dec(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(lean_object* v_word_652_, lean_object* v_result_653_, lean_object* v_patternIdx_654_, lean_object* v_wordIdx_655_){
_start:
{
uint16_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(v_word_652_, v_result_653_, v_patternIdx_654_, v_wordIdx_655_);
lean_dec(v_wordIdx_655_);
lean_dec(v_patternIdx_654_);
lean_dec_ref(v_result_653_);
lean_dec_ref(v_word_652_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(lean_object* v_word_658_, lean_object* v_result_659_, lean_object* v_patternIdx_660_, lean_object* v_wordIdx_661_){
_start:
{
uint16_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint16_t v___x_673_; 
v___x_662_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_663_ = lean_string_length(v_word_658_);
v___x_664_ = lean_nat_mul(v_patternIdx_660_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(2u);
v___x_666_ = lean_nat_mul(v___x_664_, v___x_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_nat_mul(v_wordIdx_661_, v___x_665_);
v___x_668_ = lean_nat_add(v___x_666_, v___x_667_);
lean_dec(v___x_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v___x_668_, v___x_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(v___x_662_);
v___x_672_ = lean_array_get(v___x_671_, v_result_659_, v___x_670_);
lean_dec(v___x_670_);
lean_dec(v___x_671_);
v___x_673_ = lean_unbox(v___x_672_);
lean_dec(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(lean_object* v_word_674_, lean_object* v_result_675_, lean_object* v_patternIdx_676_, lean_object* v_wordIdx_677_){
_start:
{
uint16_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(v_word_674_, v_result_675_, v_patternIdx_676_, v_wordIdx_677_);
lean_dec(v_wordIdx_677_);
lean_dec(v_patternIdx_676_);
lean_dec_ref(v_result_675_);
lean_dec_ref(v_word_674_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(lean_object* v_word_680_, lean_object* v_result_681_, lean_object* v_patternIdx_682_, lean_object* v_wordIdx_683_, uint16_t v_missValue_684_, uint16_t v_matchValue_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_idx_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_686_ = lean_string_length(v_word_680_);
v___x_687_ = lean_nat_mul(v_patternIdx_682_, v___x_686_);
v___x_688_ = lean_unsigned_to_nat(2u);
v___x_689_ = lean_nat_mul(v___x_687_, v___x_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_nat_mul(v_wordIdx_683_, v___x_688_);
v_idx_691_ = lean_nat_add(v___x_689_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(v_missValue_684_);
v___x_693_ = lean_array_set(v_result_681_, v_idx_691_, v___x_692_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_idx_691_, v___x_694_);
lean_dec(v_idx_691_);
v___x_696_ = lean_box(v_matchValue_685_);
v___x_697_ = lean_array_set(v___x_693_, v___x_695_, v___x_696_);
lean_dec(v___x_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(lean_object* v_word_698_, lean_object* v_result_699_, lean_object* v_patternIdx_700_, lean_object* v_wordIdx_701_, lean_object* v_missValue_702_, lean_object* v_matchValue_703_){
_start:
{
uint16_t v_missValue_boxed_704_; uint16_t v_matchValue_boxed_705_; lean_object* v_res_706_; 
v_missValue_boxed_704_ = lean_unbox(v_missValue_702_);
v_matchValue_boxed_705_ = lean_unbox(v_matchValue_703_);
v_res_706_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(v_word_698_, v_result_699_, v_patternIdx_700_, v_wordIdx_701_, v_missValue_boxed_704_, v_matchValue_boxed_705_);
lean_dec(v_wordIdx_701_);
lean_dec(v_patternIdx_700_);
lean_dec_ref(v_word_698_);
return v_res_706_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0(void){
_start:
{
lean_object* v___x_707_; uint16_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_int16_of_nat(v___x_707_);
return v___x_708_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1(void){
_start:
{
lean_object* v___x_709_; uint16_t v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_int16_of_nat(v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(uint8_t v_wordRole_711_, uint8_t v_wordStart_712_){
_start:
{
if (v_wordStart_712_ == 0)
{
if (v_wordRole_711_ == 0)
{
uint16_t v___x_713_; 
v___x_713_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
return v___x_713_;
}
else
{
uint16_t v___x_714_; 
v___x_714_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
return v___x_714_;
}
}
else
{
uint16_t v___x_715_; 
v___x_715_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(lean_object* v_wordRole_716_, lean_object* v_wordStart_717_){
_start:
{
uint8_t v_wordRole_boxed_718_; uint8_t v_wordStart_boxed_719_; uint16_t v_res_720_; lean_object* v_r_721_; 
v_wordRole_boxed_718_ = lean_unbox(v_wordRole_716_);
v_wordStart_boxed_719_ = lean_unbox(v_wordStart_717_);
v_res_720_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v_wordRole_boxed_718_, v_wordStart_boxed_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(uint32_t v_patternChar_722_, uint32_t v_wordChar_723_, uint8_t v_patternRole_724_, uint8_t v_wordRole_725_){
_start:
{
uint8_t v___y_727_; uint8_t v___y_728_; uint32_t v___y_732_; uint32_t v___y_733_; uint32_t v___y_739_; uint32_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 65;
v___x_747_ = lean_uint32_dec_le(v___x_746_, v_patternChar_722_);
if (v___x_747_ == 0)
{
v___y_739_ = v_patternChar_722_;
goto v___jp_738_;
}
else
{
uint32_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 90;
v___x_749_ = lean_uint32_dec_le(v_patternChar_722_, v___x_748_);
if (v___x_749_ == 0)
{
v___y_739_ = v_patternChar_722_;
goto v___jp_738_;
}
else
{
uint32_t v___x_750_; uint32_t v___x_751_; 
v___x_750_ = 32;
v___x_751_ = lean_uint32_add(v_patternChar_722_, v___x_750_);
v___y_739_ = v___x_751_;
goto v___jp_738_;
}
}
v___jp_726_:
{
if (v_wordRole_725_ == 0)
{
uint8_t v___x_729_; 
v___x_729_ = lean_bool_not(v___y_727_);
if (v___x_729_ == 0)
{
return v___y_727_;
}
else
{
return v___y_728_;
}
}
else
{
uint8_t v___x_730_; 
v___x_730_ = lean_bool_not(v___y_728_);
if (v___x_730_ == 0)
{
return v___y_727_;
}
else
{
return v___y_728_;
}
}
}
v___jp_731_:
{
uint8_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_uint32_dec_eq(v___y_732_, v___y_733_);
v___x_735_ = lean_bool_not(v___x_734_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
v___x_736_ = 1;
if (v_patternRole_724_ == 0)
{
v___y_727_ = v___x_736_;
v___y_728_ = v___x_735_;
goto v___jp_726_;
}
else
{
if (v___x_735_ == 0)
{
return v___x_736_;
}
else
{
v___y_727_ = v___x_736_;
v___y_728_ = v___x_735_;
goto v___jp_726_;
}
}
}
else
{
uint8_t v___x_737_; 
v___x_737_ = 0;
return v___x_737_;
}
}
v___jp_738_:
{
uint32_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = 65;
v___x_741_ = lean_uint32_dec_le(v___x_740_, v_wordChar_723_);
if (v___x_741_ == 0)
{
v___y_732_ = v___y_739_;
v___y_733_ = v_wordChar_723_;
goto v___jp_731_;
}
else
{
uint32_t v___x_742_; uint8_t v___x_743_; 
v___x_742_ = 90;
v___x_743_ = lean_uint32_dec_le(v_wordChar_723_, v___x_742_);
if (v___x_743_ == 0)
{
v___y_732_ = v___y_739_;
v___y_733_ = v_wordChar_723_;
goto v___jp_731_;
}
else
{
uint32_t v___x_744_; uint32_t v___x_745_; 
v___x_744_ = 32;
v___x_745_ = lean_uint32_add(v_wordChar_723_, v___x_744_);
v___y_732_ = v___y_739_;
v___y_733_ = v___x_745_;
goto v___jp_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(lean_object* v_patternChar_752_, lean_object* v_wordChar_753_, lean_object* v_patternRole_754_, lean_object* v_wordRole_755_){
_start:
{
uint32_t v_patternChar_boxed_756_; uint32_t v_wordChar_boxed_757_; uint8_t v_patternRole_boxed_758_; uint8_t v_wordRole_boxed_759_; uint8_t v_res_760_; lean_object* v_r_761_; 
v_patternChar_boxed_756_ = lean_unbox_uint32(v_patternChar_752_);
lean_dec(v_patternChar_752_);
v_wordChar_boxed_757_ = lean_unbox_uint32(v_wordChar_753_);
lean_dec(v_wordChar_753_);
v_patternRole_boxed_758_ = lean_unbox(v_patternRole_754_);
v_wordRole_boxed_759_ = lean_unbox(v_wordRole_755_);
v_res_760_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v_patternChar_boxed_756_, v_wordChar_boxed_757_, v_patternRole_boxed_758_, v_wordRole_boxed_759_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0(void){
_start:
{
lean_object* v___x_762_; uint16_t v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(2u);
v___x_763_ = lean_int16_of_nat(v___x_762_);
return v___x_763_;
}
}
static uint16_t _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1(void){
_start:
{
uint16_t v_score_764_; uint16_t v_score_765_; 
v_score_764_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v_score_765_ = lean_int16_add(v_score_764_, v_score_764_);
return v_score_765_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(lean_object* v_pattern_766_, lean_object* v_word_767_, lean_object* v_patternIdx_768_, lean_object* v_wordIdx_769_, uint8_t v_patternRole_770_, uint8_t v_wordRole_771_, uint16_t v_consecutive_772_){
_start:
{
uint16_t v_score_774_; uint16_t v_score_779_; uint16_t v___y_785_; uint8_t v___y_786_; lean_object* v___x_789_; uint16_t v_score_791_; uint16_t v_score_798_; uint8_t v___y_802_; uint32_t v___x_803_; uint32_t v___x_804_; uint8_t v___x_805_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v_score_798_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_803_ = lean_string_utf8_get(v_pattern_766_, v_patternIdx_768_);
v___x_804_ = lean_string_utf8_get(v_word_767_, v_wordIdx_769_);
v___x_805_ = lean_uint32_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
if (v_patternRole_770_ == 0)
{
if (v_wordRole_771_ == 0)
{
goto v___jp_799_;
}
else
{
v___y_802_ = v___x_805_;
goto v___jp_801_;
}
}
else
{
v___y_802_ = v___x_805_;
goto v___jp_801_;
}
}
else
{
v___y_802_ = v___x_805_;
goto v___jp_801_;
}
v___jp_773_:
{
uint16_t v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_776_ = lean_int16_dec_le(v_consecutive_772_, v___x_775_);
if (v___x_776_ == 0)
{
uint16_t v_score_777_; 
v_score_777_ = lean_int16_add(v_score_774_, v_consecutive_772_);
return v_score_777_;
}
else
{
return v_score_774_;
}
}
v___jp_778_:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_nat_dec_eq(v_wordIdx_769_, v___x_780_);
if (v___x_781_ == 0)
{
v_score_774_ = v_score_779_;
goto v___jp_773_;
}
else
{
uint16_t v___x_782_; uint16_t v_score_783_; 
v___x_782_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
v_score_783_ = lean_int16_add(v_score_779_, v___x_782_);
v_score_774_ = v_score_783_;
goto v___jp_773_;
}
}
v___jp_784_:
{
if (v___y_786_ == 0)
{
v_score_779_ = v___y_785_;
goto v___jp_778_;
}
else
{
uint16_t v___x_787_; uint16_t v_score_788_; 
v___x_787_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
v_score_788_ = lean_int16_add(v___y_785_, v___x_787_);
v_score_779_ = v_score_788_;
goto v___jp_778_;
}
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_string_length(v_word_767_);
v___x_793_ = lean_nat_sub(v___x_792_, v___x_789_);
v___x_794_ = lean_nat_dec_eq(v_wordIdx_769_, v___x_793_);
lean_dec(v___x_793_);
if (v___x_794_ == 0)
{
v___y_785_ = v_score_791_;
v___y_786_ = v___x_794_;
goto v___jp_784_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_string_length(v_pattern_766_);
v___x_796_ = lean_nat_sub(v___x_795_, v___x_789_);
v___x_797_ = lean_nat_dec_eq(v_patternIdx_768_, v___x_796_);
lean_dec(v___x_796_);
v___y_785_ = v_score_791_;
v___y_786_ = v___x_797_;
goto v___jp_784_;
}
}
v___jp_799_:
{
uint16_t v_score_800_; 
v_score_800_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
v_score_791_ = v_score_800_;
goto v___jp_790_;
}
v___jp_801_:
{
if (v___y_802_ == 0)
{
v_score_791_ = v_score_798_;
goto v___jp_790_;
}
else
{
goto v___jp_799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(lean_object* v_pattern_806_, lean_object* v_word_807_, lean_object* v_patternIdx_808_, lean_object* v_wordIdx_809_, lean_object* v_patternRole_810_, lean_object* v_wordRole_811_, lean_object* v_consecutive_812_){
_start:
{
uint8_t v_patternRole_boxed_813_; uint8_t v_wordRole_boxed_814_; uint16_t v_consecutive_boxed_815_; uint16_t v_res_816_; lean_object* v_r_817_; 
v_patternRole_boxed_813_ = lean_unbox(v_patternRole_810_);
v_wordRole_boxed_814_ = lean_unbox(v_wordRole_811_);
v_consecutive_boxed_815_ = lean_unbox(v_consecutive_812_);
v_res_816_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_806_, v_word_807_, v_patternIdx_808_, v_wordIdx_809_, v_patternRole_boxed_813_, v_wordRole_boxed_814_, v_consecutive_boxed_815_);
lean_dec(v_wordIdx_809_);
lean_dec(v_patternIdx_808_);
lean_dec_ref(v_word_807_);
lean_dec_ref(v_pattern_806_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT uint16_t l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(lean_object* v_msg_818_){
_start:
{
uint16_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint16_t v___x_822_; 
v___x_819_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_820_ = lean_box(v___x_819_);
v___x_821_ = lean_panic_fn_borrowed(v___x_820_, v_msg_818_);
lean_dec(v___x_820_);
v___x_822_ = lean_unbox(v___x_821_);
lean_dec(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(lean_object* v_msg_823_){
_start:
{
uint16_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_823_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(lean_object* v___x_826_, lean_object* v_a_827_, uint16_t v_x_828_){
_start:
{
uint16_t v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_830_ = lean_int16_dec_le(v_x_828_, v___x_829_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = lean_nat_dec_le(v___x_826_, v_a_827_);
if (v___x_831_ == 0)
{
return v_x_828_;
}
else
{
uint16_t v___x_832_; uint16_t v___x_833_; 
v___x_832_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_833_ = lean_int16_add(v_x_828_, v___x_832_);
return v___x_833_;
}
}
else
{
return v_x_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(lean_object* v___x_834_, lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
uint16_t v_x_boxed_837_; uint16_t v_res_838_; lean_object* v_r_839_; 
v_x_boxed_837_ = lean_unbox(v_x_836_);
v_res_838_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_834_, v_a_835_, v_x_boxed_837_);
lean_dec(v_a_835_);
lean_dec(v___x_834_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(lean_object* v_pattern_840_, lean_object* v_word_841_, lean_object* v_a_842_, lean_object* v_a_843_, uint8_t v___x_844_, uint8_t v___x_845_, lean_object* v___x_846_, uint16_t v_x_847_){
_start:
{
uint16_t v_matchScore_848_; uint8_t v___x_849_; 
v_matchScore_848_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_849_ = lean_int16_dec_le(v_x_847_, v_matchScore_848_);
if (v___x_849_ == 0)
{
uint16_t v___x_850_; uint16_t v___x_851_; uint16_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint16_t v___x_855_; uint16_t v___x_856_; 
v___x_850_ = l_instInhabitedInt16;
v___x_851_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_840_, v_word_841_, v_a_842_, v_a_843_, v___x_844_, v___x_845_, v_matchScore_848_);
v___x_852_ = lean_int16_add(v_x_847_, v___x_851_);
v___x_853_ = lean_box(v___x_850_);
v___x_854_ = lean_array_get(v___x_853_, v___x_846_, v_a_843_);
lean_dec(v___x_853_);
v___x_855_ = lean_unbox(v___x_854_);
lean_dec(v___x_854_);
v___x_856_ = lean_int16_sub(v___x_852_, v___x_855_);
return v___x_856_;
}
else
{
return v_x_847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(lean_object* v_pattern_857_, lean_object* v_word_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v_x_864_){
_start:
{
uint8_t v___x_3259__boxed_865_; uint8_t v___x_3260__boxed_866_; uint16_t v_x_boxed_867_; uint16_t v_res_868_; lean_object* v_r_869_; 
v___x_3259__boxed_865_ = lean_unbox(v___x_861_);
v___x_3260__boxed_866_ = lean_unbox(v___x_862_);
v_x_boxed_867_ = lean_unbox(v_x_864_);
v_res_868_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_857_, v_word_858_, v_a_859_, v_a_860_, v___x_3259__boxed_865_, v___x_3260__boxed_866_, v___x_863_, v_x_boxed_867_);
lean_dec_ref(v___x_863_);
lean_dec(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_word_858_);
lean_dec_ref(v_pattern_857_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT uint16_t l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(lean_object* v_pattern_870_, lean_object* v_word_871_, lean_object* v_a_872_, lean_object* v_a_873_, uint8_t v___x_874_, uint8_t v___x_875_, uint16_t v___x_876_, uint16_t v_x_877_){
_start:
{
uint16_t v___y_879_; uint16_t v___x_882_; uint8_t v___x_883_; 
v___x_882_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_883_ = lean_int16_dec_le(v_x_877_, v___x_882_);
if (v___x_883_ == 0)
{
uint8_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = lean_int16_dec_eq(v___x_876_, v___x_882_);
v___x_885_ = lean_bool_not(v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; uint16_t v___x_887_; 
v___x_886_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_887_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_886_);
v___y_879_ = v___x_887_;
goto v___jp_878_;
}
else
{
v___y_879_ = v___x_876_;
goto v___jp_878_;
}
}
else
{
return v_x_877_;
}
v___jp_878_:
{
uint16_t v___x_880_; uint16_t v___x_881_; 
v___x_880_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_870_, v_word_871_, v_a_872_, v_a_873_, v___x_874_, v___x_875_, v___y_879_);
v___x_881_ = lean_int16_add(v_x_877_, v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(lean_object* v_pattern_888_, lean_object* v_word_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v_x_895_){
_start:
{
uint8_t v___x_3299__boxed_896_; uint8_t v___x_3300__boxed_897_; uint16_t v___x_3301__boxed_898_; uint16_t v_x_boxed_899_; uint16_t v_res_900_; lean_object* v_r_901_; 
v___x_3299__boxed_896_ = lean_unbox(v___x_892_);
v___x_3300__boxed_897_ = lean_unbox(v___x_893_);
v___x_3301__boxed_898_ = lean_unbox(v___x_894_);
v_x_boxed_899_ = lean_unbox(v_x_895_);
v_res_900_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_888_, v_word_889_, v_a_890_, v_a_891_, v___x_3299__boxed_896_, v___x_3300__boxed_897_, v___x_3301__boxed_898_, v_x_boxed_899_);
lean_dec(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_word_889_);
lean_dec_ref(v_pattern_888_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(lean_object* v_word_902_, lean_object* v_a_903_, lean_object* v_pattern_904_, lean_object* v_patternRoles_905_, lean_object* v_wordRoles_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v_range_909_, lean_object* v_b_910_, lean_object* v_i_911_){
_start:
{
lean_object* v_stop_912_; lean_object* v_step_913_; uint8_t v___x_914_; 
v_stop_912_ = lean_ctor_get(v_range_909_, 1);
v_step_913_ = lean_ctor_get(v_range_909_, 2);
v___x_914_ = lean_nat_dec_lt(v_i_911_, v_stop_912_);
if (v___x_914_ == 0)
{
lean_dec(v_i_911_);
return v_b_910_;
}
else
{
lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1031_; 
v_fst_915_ = lean_ctor_get(v_b_910_, 0);
v_snd_916_ = lean_ctor_get(v_b_910_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_b_910_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_918_ = v_b_910_;
v_isShared_919_ = v_isSharedCheck_1031_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_916_);
lean_inc(v_fst_915_);
lean_dec(v_b_910_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1031_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; uint16_t v_matchScore_921_; lean_object* v___x_922_; uint16_t v___y_924_; lean_object* v_runLengths_925_; uint16_t v_matchScore_926_; lean_object* v___y_944_; uint16_t v___y_945_; uint16_t v___y_946_; uint16_t v___y_949_; uint8_t v___x_1012_; 
v___x_920_ = 0;
v_matchScore_921_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_dec_le(v___x_922_, v_i_911_);
if (v___x_1012_ == 0)
{
v___y_949_ = v_matchScore_921_;
goto v___jp_948_;
}
else
{
lean_object* v___x_1013_; uint16_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint16_t v___x_1026_; uint16_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1013_ = lean_nat_sub(v_i_911_, v___x_922_);
v___x_1014_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1015_ = lean_string_length(v_word_902_);
v___x_1016_ = lean_nat_mul(v_a_903_, v___x_1015_);
v___x_1017_ = lean_unsigned_to_nat(2u);
v___x_1018_ = lean_nat_mul(v___x_1016_, v___x_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_nat_mul(v___x_1013_, v___x_1017_);
lean_dec(v___x_1013_);
v___x_1020_ = lean_nat_add(v___x_1018_, v___x_1019_);
lean_dec(v___x_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(v___x_1014_);
v___x_1022_ = lean_array_get(v___x_1021_, v_fst_915_, v___x_1020_);
lean_dec(v___x_1021_);
v___x_1023_ = lean_nat_add(v___x_1020_, v___x_922_);
lean_dec(v___x_1020_);
v___x_1024_ = lean_box(v___x_1014_);
v___x_1025_ = lean_array_get(v___x_1024_, v_fst_915_, v___x_1023_);
lean_dec(v___x_1023_);
lean_dec(v___x_1024_);
v___x_1026_ = lean_unbox(v___x_1022_);
v___x_1027_ = lean_unbox(v___x_1025_);
v___x_1028_ = lean_int16_dec_le(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
uint16_t v___x_1029_; 
lean_dec(v___x_1025_);
v___x_1029_ = lean_unbox(v___x_1022_);
lean_dec(v___x_1022_);
v___y_949_ = v___x_1029_;
goto v___jp_948_;
}
else
{
uint16_t v___x_1030_; 
lean_dec(v___x_1022_);
v___x_1030_ = lean_unbox(v___x_1025_);
lean_dec(v___x_1025_);
v___y_949_ = v___x_1030_;
goto v___jp_948_;
}
}
v___jp_923_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_idx_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_927_ = lean_string_length(v_word_902_);
v___x_928_ = lean_nat_mul(v_a_903_, v___x_927_);
v___x_929_ = lean_unsigned_to_nat(2u);
v___x_930_ = lean_nat_mul(v___x_928_, v___x_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_nat_mul(v_i_911_, v___x_929_);
v_idx_932_ = lean_nat_add(v___x_930_, v___x_931_);
lean_dec(v___x_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(v___y_924_);
v___x_934_ = lean_array_set(v_fst_915_, v_idx_932_, v___x_933_);
v___x_935_ = lean_nat_add(v_idx_932_, v___x_922_);
lean_dec(v_idx_932_);
v___x_936_ = lean_box(v_matchScore_926_);
v___x_937_ = lean_array_set(v___x_934_, v___x_935_, v___x_936_);
lean_dec(v___x_935_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_runLengths_925_);
lean_ctor_set(v___x_918_, 0, v___x_937_);
v___x_939_ = v___x_918_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_runLengths_925_);
v___x_939_ = v_reuseFailAlloc_942_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = lean_nat_add(v_i_911_, v_step_913_);
lean_dec(v_i_911_);
v_b_910_ = v___x_939_;
v_i_911_ = v___x_940_;
goto _start;
}
}
v___jp_943_:
{
uint16_t v___x_947_; 
v___x_947_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_908_, v_i_911_, v___y_946_);
v___y_924_ = v___y_945_;
v_runLengths_925_ = v___y_944_;
v_matchScore_926_ = v___x_947_;
goto v___jp_923_;
}
v___jp_948_:
{
uint32_t v___x_950_; uint32_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_950_ = lean_string_utf8_get(v_pattern_904_, v_a_903_);
v___x_951_ = lean_string_utf8_get(v_word_902_, v_i_911_);
v___x_952_ = lean_box(v___x_920_);
v___x_953_ = lean_array_get(v___x_952_, v_patternRoles_905_, v_a_903_);
lean_dec(v___x_952_);
v___x_954_ = lean_box(v___x_920_);
v___x_955_ = lean_array_get(v___x_954_, v_wordRoles_906_, v_i_911_);
lean_dec(v___x_954_);
v___x_956_ = lean_unbox(v___x_953_);
v___x_957_ = lean_unbox(v___x_955_);
v___x_958_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_950_, v___x_951_, v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v___x_955_);
lean_dec(v___x_953_);
v___y_924_ = v___y_949_;
v_runLengths_925_ = v_snd_916_;
v_matchScore_926_ = v_matchScore_921_;
goto v___jp_923_;
}
else
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_le(v___x_922_, v_a_903_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint16_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; uint8_t v___x_967_; uint16_t v___x_968_; uint16_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint16_t v___x_972_; uint16_t v___x_973_; uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_960_ = lean_string_length(v_word_902_);
v___x_961_ = lean_nat_mul(v_a_903_, v___x_960_);
v___x_962_ = lean_nat_add(v___x_961_, v_i_911_);
lean_dec(v___x_961_);
v___x_963_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_964_ = lean_box(v___x_963_);
v___x_965_ = lean_array_set(v_snd_916_, v___x_962_, v___x_964_);
lean_dec(v___x_962_);
v___x_966_ = lean_unbox(v___x_953_);
lean_dec(v___x_953_);
v___x_967_ = lean_unbox(v___x_955_);
lean_dec(v___x_955_);
v___x_968_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_904_, v_word_902_, v_a_903_, v_i_911_, v___x_966_, v___x_967_, v_matchScore_921_);
v___x_969_ = l_instInhabitedInt16;
v___x_970_ = lean_box(v___x_969_);
v___x_971_ = lean_array_get(v___x_970_, v___x_907_, v_i_911_);
lean_dec(v___x_970_);
v___x_972_ = lean_unbox(v___x_971_);
lean_dec(v___x_971_);
v___x_973_ = lean_int16_sub(v___x_968_, v___x_972_);
v___x_974_ = lean_int16_dec_eq(v___x_973_, v_matchScore_921_);
v___x_975_ = lean_bool_not(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; uint16_t v___x_977_; 
v___x_976_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
v___x_977_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_976_);
v___y_924_ = v___y_949_;
v_runLengths_925_ = v___x_965_;
v_matchScore_926_ = v___x_977_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_949_;
v_runLengths_925_ = v___x_965_;
v_matchScore_926_ = v___x_973_;
goto v___jp_923_;
}
}
else
{
uint16_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint16_t v___x_986_; uint16_t v___x_987_; uint16_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint16_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; uint8_t v___x_1001_; uint16_t v___x_1002_; uint16_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; uint8_t v___x_1008_; uint16_t v___x_1009_; uint16_t v___x_1010_; uint8_t v___x_1011_; 
v___x_978_ = l_instInhabitedInt16;
v___x_979_ = lean_nat_sub(v_a_903_, v___x_922_);
v___x_980_ = lean_nat_sub(v_i_911_, v___x_922_);
v___x_981_ = lean_string_length(v_word_902_);
v___x_982_ = lean_nat_mul(v___x_979_, v___x_981_);
lean_dec(v___x_979_);
v___x_983_ = lean_nat_add(v___x_982_, v___x_980_);
v___x_984_ = lean_box(v___x_978_);
v___x_985_ = lean_array_get(v___x_984_, v_snd_916_, v___x_983_);
lean_dec(v___x_983_);
lean_dec(v___x_984_);
v___x_986_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_987_ = lean_unbox(v___x_985_);
lean_dec(v___x_985_);
v___x_988_ = lean_int16_add(v___x_987_, v___x_986_);
v___x_989_ = lean_nat_mul(v_a_903_, v___x_981_);
v___x_990_ = lean_nat_add(v___x_989_, v_i_911_);
lean_dec(v___x_989_);
v___x_991_ = lean_box(v___x_988_);
v___x_992_ = lean_array_set(v_snd_916_, v___x_990_, v___x_991_);
lean_dec(v___x_990_);
v___x_993_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_994_ = lean_unsigned_to_nat(2u);
v___x_995_ = lean_nat_mul(v___x_982_, v___x_994_);
lean_dec(v___x_982_);
v___x_996_ = lean_nat_mul(v___x_980_, v___x_994_);
lean_dec(v___x_980_);
v___x_997_ = lean_nat_add(v___x_995_, v___x_996_);
lean_dec(v___x_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(v___x_993_);
v___x_999_ = lean_array_get(v___x_998_, v_fst_915_, v___x_997_);
lean_dec(v___x_998_);
v___x_1000_ = lean_unbox(v___x_953_);
v___x_1001_ = lean_unbox(v___x_955_);
v___x_1002_ = lean_unbox(v___x_999_);
lean_dec(v___x_999_);
v___x_1003_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_904_, v_word_902_, v_a_903_, v_i_911_, v___x_1000_, v___x_1001_, v___x_907_, v___x_1002_);
v___x_1004_ = lean_nat_add(v___x_997_, v___x_922_);
lean_dec(v___x_997_);
v___x_1005_ = lean_box(v___x_993_);
v___x_1006_ = lean_array_get(v___x_1005_, v_fst_915_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_unbox(v___x_953_);
lean_dec(v___x_953_);
v___x_1008_ = lean_unbox(v___x_955_);
lean_dec(v___x_955_);
v___x_1009_ = lean_unbox(v___x_1006_);
lean_dec(v___x_1006_);
v___x_1010_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_904_, v_word_902_, v_a_903_, v_i_911_, v___x_1007_, v___x_1008_, v___x_988_, v___x_1009_);
v___x_1011_ = lean_int16_dec_le(v___x_1003_, v___x_1010_);
if (v___x_1011_ == 0)
{
v___y_944_ = v___x_992_;
v___y_945_ = v___y_949_;
v___y_946_ = v___x_1003_;
goto v___jp_943_;
}
else
{
v___y_944_ = v___x_992_;
v___y_945_ = v___y_949_;
v___y_946_ = v___x_1010_;
goto v___jp_943_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(lean_object* v_word_1032_, lean_object* v_a_1033_, lean_object* v_pattern_1034_, lean_object* v_patternRoles_1035_, lean_object* v_wordRoles_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_range_1039_, lean_object* v_b_1040_, lean_object* v_i_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1032_, v_a_1033_, v_pattern_1034_, v_patternRoles_1035_, v_wordRoles_1036_, v___x_1037_, v___x_1038_, v_range_1039_, v_b_1040_, v_i_1041_);
lean_dec_ref(v_range_1039_);
lean_dec(v___x_1038_);
lean_dec_ref(v___x_1037_);
lean_dec_ref(v_wordRoles_1036_);
lean_dec_ref(v_patternRoles_1035_);
lean_dec_ref(v_pattern_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_word_1032_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(lean_object* v___x_1043_, lean_object* v___x_1044_, lean_object* v_word_1045_, lean_object* v_pattern_1046_, lean_object* v_patternRoles_1047_, lean_object* v_wordRoles_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_range_1051_, lean_object* v_b_1052_, lean_object* v_i_1053_){
_start:
{
lean_object* v_stop_1054_; lean_object* v_step_1055_; uint8_t v___x_1056_; 
v_stop_1054_ = lean_ctor_get(v_range_1051_, 1);
v_step_1055_ = lean_ctor_get(v_range_1051_, 2);
v___x_1056_ = lean_nat_dec_lt(v_i_1053_, v_stop_1054_);
if (v___x_1056_ == 0)
{
lean_dec(v_i_1053_);
return v_b_1052_;
}
else
{
lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1082_; 
v_fst_1057_ = lean_ctor_get(v_b_1052_, 0);
v_snd_1058_ = lean_ctor_get(v_b_1052_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_b_1052_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1060_ = v_b_1052_;
v_isShared_1061_ = v_isSharedCheck_1082_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snd_1058_);
lean_inc(v_fst_1057_);
lean_dec(v_b_1052_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1082_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_sub(v___x_1043_, v_i_1053_);
v___x_1064_ = lean_nat_sub(v___x_1063_, v___x_1062_);
lean_dec(v___x_1063_);
v___x_1065_ = lean_nat_sub(v___x_1044_, v___x_1064_);
lean_dec(v___x_1064_);
lean_inc(v_i_1053_);
v___x_1066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1066_, 0, v_i_1053_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
lean_ctor_set(v___x_1066_, 2, v___x_1062_);
if (v_isShared_1061_ == 0)
{
v___x_1068_ = v___x_1060_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_fst_1057_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_snd_1058_);
v___x_1068_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1080_; 
lean_inc(v_i_1053_);
v___x_1069_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1045_, v_i_1053_, v_pattern_1046_, v_patternRoles_1047_, v_wordRoles_1048_, v___x_1049_, v___x_1050_, v___x_1066_, v___x_1068_, v_i_1053_);
lean_dec_ref_known(v___x_1066_, 3);
v_fst_1070_ = lean_ctor_get(v___x_1069_, 0);
v_snd_1071_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1073_ = v___x_1069_;
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_snd_1071_);
lean_inc(v_fst_1070_);
lean_dec(v___x_1069_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_fst_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_snd_1071_);
v___x_1076_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_nat_add(v_i_1053_, v_step_1055_);
lean_dec(v_i_1053_);
v_b_1052_ = v___x_1076_;
v_i_1053_ = v___x_1077_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_word_1085_, lean_object* v_pattern_1086_, lean_object* v_patternRoles_1087_, lean_object* v_wordRoles_1088_, lean_object* v___x_1089_, lean_object* v___x_1090_, lean_object* v_range_1091_, lean_object* v_b_1092_, lean_object* v_i_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1083_, v___x_1084_, v_word_1085_, v_pattern_1086_, v_patternRoles_1087_, v_wordRoles_1088_, v___x_1089_, v___x_1090_, v_range_1091_, v_b_1092_, v_i_1093_);
lean_dec_ref(v_range_1091_);
lean_dec(v___x_1090_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v_wordRoles_1088_);
lean_dec_ref(v_patternRoles_1087_);
lean_dec_ref(v_pattern_1086_);
lean_dec_ref(v_word_1085_);
lean_dec(v___x_1084_);
lean_dec(v___x_1083_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(lean_object* v_word_1095_, lean_object* v_pattern_1096_, lean_object* v_patternRoles_1097_, lean_object* v_wordRoles_1098_, lean_object* v___x_1099_, lean_object* v___x_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v_range_1103_, lean_object* v_b_1104_, lean_object* v_i_1105_){
_start:
{
lean_object* v_stop_1106_; lean_object* v_step_1107_; uint8_t v___x_1108_; 
v_stop_1106_ = lean_ctor_get(v_range_1103_, 1);
v_step_1107_ = lean_ctor_get(v_range_1103_, 2);
v___x_1108_ = lean_nat_dec_lt(v_i_1105_, v_stop_1106_);
if (v___x_1108_ == 0)
{
lean_dec(v_i_1105_);
return v_b_1104_;
}
else
{
lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1134_; 
v_fst_1109_ = lean_ctor_get(v_b_1104_, 0);
v_snd_1110_ = lean_ctor_get(v_b_1104_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_b_1104_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1112_ = v_b_1104_;
v_isShared_1113_ = v_isSharedCheck_1134_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_snd_1110_);
lean_inc(v_fst_1109_);
lean_dec(v_b_1104_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1134_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_sub(v___x_1101_, v_i_1105_);
v___x_1116_ = lean_nat_sub(v___x_1115_, v___x_1114_);
lean_dec(v___x_1115_);
v___x_1117_ = lean_nat_sub(v___x_1102_, v___x_1116_);
lean_dec(v___x_1116_);
lean_inc(v_i_1105_);
v___x_1118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1118_, 0, v_i_1105_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
lean_ctor_set(v___x_1118_, 2, v___x_1114_);
if (v_isShared_1113_ == 0)
{
v___x_1120_ = v___x_1112_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_fst_1109_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_snd_1110_);
v___x_1120_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
lean_inc(v_i_1105_);
v___x_1121_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1095_, v_i_1105_, v_pattern_1096_, v_patternRoles_1097_, v_wordRoles_1098_, v___x_1099_, v___x_1100_, v___x_1118_, v___x_1120_, v_i_1105_);
lean_dec_ref_known(v___x_1118_, 3);
v_fst_1122_ = lean_ctor_get(v___x_1121_, 0);
v_snd_1123_ = lean_ctor_get(v___x_1121_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snd_1123_);
lean_inc(v_fst_1122_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_fst_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_snd_1123_);
v___x_1128_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_nat_add(v_i_1105_, v_step_1107_);
lean_dec(v_i_1105_);
v___x_1130_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1101_, v___x_1102_, v_word_1095_, v_pattern_1096_, v_patternRoles_1097_, v_wordRoles_1098_, v___x_1099_, v___x_1100_, v_range_1103_, v___x_1128_, v___x_1129_);
return v___x_1130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(lean_object* v_word_1135_, lean_object* v_pattern_1136_, lean_object* v_patternRoles_1137_, lean_object* v_wordRoles_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v_range_1143_, lean_object* v_b_1144_, lean_object* v_i_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1135_, v_pattern_1136_, v_patternRoles_1137_, v_wordRoles_1138_, v___x_1139_, v___x_1140_, v___x_1141_, v___x_1142_, v_range_1143_, v_b_1144_, v_i_1145_);
lean_dec_ref(v_range_1143_);
lean_dec(v___x_1142_);
lean_dec(v___x_1141_);
lean_dec(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v_wordRoles_1138_);
lean_dec_ref(v_patternRoles_1137_);
lean_dec_ref(v_pattern_1136_);
lean_dec_ref(v_word_1135_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(lean_object* v_wordRoles_1147_, lean_object* v_range_1148_, lean_object* v_b_1149_, lean_object* v_i_1150_){
_start:
{
lean_object* v_stop_1151_; lean_object* v_step_1152_; uint8_t v___x_1153_; 
v_stop_1151_ = lean_ctor_get(v_range_1148_, 1);
v_step_1152_ = lean_ctor_get(v_range_1148_, 2);
v___x_1153_ = lean_nat_dec_lt(v_i_1150_, v_stop_1151_);
if (v___x_1153_ == 0)
{
lean_dec(v_i_1150_);
return v_b_1149_;
}
else
{
lean_object* v_snd_1154_; lean_object* v_snd_1155_; lean_object* v_fst_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1215_; 
v_snd_1154_ = lean_ctor_get(v_b_1149_, 1);
lean_inc(v_snd_1154_);
v_snd_1155_ = lean_ctor_get(v_snd_1154_, 1);
lean_inc(v_snd_1155_);
v_fst_1156_ = lean_ctor_get(v_b_1149_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_b_1149_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_b_1149_, 1);
lean_dec(v_unused_1216_);
v___x_1158_ = v_b_1149_;
v_isShared_1159_ = v_isSharedCheck_1215_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_fst_1156_);
lean_dec(v_b_1149_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1215_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_fst_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1213_; 
v_fst_1160_ = lean_ctor_get(v_snd_1154_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_snd_1154_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_snd_1154_, 1);
lean_dec(v_unused_1214_);
v___x_1162_ = v_snd_1154_;
v_isShared_1163_ = v_isSharedCheck_1213_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_fst_1160_);
lean_dec(v_snd_1154_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1213_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1212_; 
v_fst_1164_ = lean_ctor_get(v_snd_1155_, 0);
v_snd_1165_ = lean_ctor_get(v_snd_1155_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_snd_1155_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1167_ = v_snd_1155_;
v_isShared_1168_ = v_isSharedCheck_1212_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_inc(v_fst_1164_);
lean_dec(v_snd_1155_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1212_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___x_1169_; lean_object* v_lastSepIdx_1170_; lean_object* v_lastSepIdx_1172_; uint16_t v_penaltyNs_1173_; uint16_t v_penaltySkip_1174_; uint16_t v_penaltyNs_1197_; uint8_t v___y_1199_; uint8_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1169_ = 0;
v_lastSepIdx_1170_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1197_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1205_ = lean_nat_dec_eq(v_i_1150_, v_lastSepIdx_1170_);
v___x_1206_ = lean_bool_not(v___x_1205_);
if (v___x_1206_ == 0)
{
v___y_1199_ = v___x_1206_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1207_ = lean_box(v___x_1169_);
v___x_1208_ = lean_array_get(v___x_1207_, v_wordRoles_1147_, v_i_1150_);
lean_dec(v___x_1207_);
v___x_1209_ = lean_unbox(v___x_1208_);
lean_dec(v___x_1208_);
if (v___x_1209_ == 2)
{
v___y_1199_ = v___x_1206_;
goto v___jp_1198_;
}
else
{
uint16_t v___x_1210_; uint16_t v___x_1211_; 
v___x_1210_ = lean_unbox(v_fst_1164_);
lean_dec(v_fst_1164_);
v___x_1211_ = lean_unbox(v_snd_1165_);
lean_dec(v_snd_1165_);
v_lastSepIdx_1172_ = v_fst_1160_;
v_penaltyNs_1173_ = v___x_1210_;
v_penaltySkip_1174_ = v___x_1211_;
goto v___jp_1171_;
}
}
v___jp_1171_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; uint16_t v___x_1179_; uint16_t v___x_1180_; uint16_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1175_ = lean_box(v___x_1169_);
v___x_1176_ = lean_array_get(v___x_1175_, v_wordRoles_1147_, v_i_1150_);
lean_dec(v___x_1175_);
v___x_1177_ = lean_nat_dec_eq(v_i_1150_, v_lastSepIdx_1170_);
v___x_1178_ = lean_unbox(v___x_1176_);
lean_dec(v___x_1176_);
v___x_1179_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_1178_, v___x_1177_);
v___x_1180_ = lean_int16_add(v_penaltySkip_1174_, v___x_1179_);
v___x_1181_ = lean_int16_add(v___x_1180_, v_penaltyNs_1173_);
v___x_1182_ = lean_box(v___x_1181_);
v___x_1183_ = lean_array_set(v_fst_1156_, v_i_1150_, v___x_1182_);
v___x_1184_ = lean_box(v_penaltyNs_1173_);
v___x_1185_ = lean_box(v___x_1180_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1185_);
lean_ctor_set(v___x_1167_, 0, v___x_1184_);
v___x_1187_ = v___x_1167_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1187_);
lean_ctor_set(v___x_1162_, 0, v_lastSepIdx_1172_);
v___x_1189_ = v___x_1162_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_lastSepIdx_1172_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v___x_1189_);
lean_ctor_set(v___x_1158_, 0, v___x_1183_);
v___x_1191_ = v___x_1158_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_nat_add(v_i_1150_, v_step_1152_);
lean_dec(v_i_1150_);
v_b_1149_ = v___x_1191_;
v_i_1150_ = v___x_1192_;
goto _start;
}
}
}
}
v___jp_1198_:
{
if (v___y_1199_ == 0)
{
uint16_t v___x_1200_; uint16_t v___x_1201_; 
v___x_1200_ = lean_unbox(v_fst_1164_);
lean_dec(v_fst_1164_);
v___x_1201_ = lean_unbox(v_snd_1165_);
lean_dec(v_snd_1165_);
v_lastSepIdx_1172_ = v_fst_1160_;
v_penaltyNs_1173_ = v___x_1200_;
v_penaltySkip_1174_ = v___x_1201_;
goto v___jp_1171_;
}
else
{
uint16_t v___x_1202_; uint16_t v___x_1203_; uint16_t v___x_1204_; 
lean_dec(v_snd_1165_);
lean_dec(v_fst_1160_);
v___x_1202_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
v___x_1203_ = lean_unbox(v_fst_1164_);
lean_dec(v_fst_1164_);
v___x_1204_ = lean_int16_add(v___x_1203_, v___x_1202_);
lean_inc(v_i_1150_);
v_lastSepIdx_1172_ = v_i_1150_;
v_penaltyNs_1173_ = v___x_1204_;
v_penaltySkip_1174_ = v_penaltyNs_1197_;
goto v___jp_1171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(lean_object* v_wordRoles_1217_, lean_object* v_range_1218_, lean_object* v_b_1219_, lean_object* v_i_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1217_, v_range_1218_, v_b_1219_, v_i_1220_);
lean_dec_ref(v_range_1218_);
lean_dec_ref(v_wordRoles_1217_);
return v_res_1221_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0(void){
_start:
{
uint16_t v_penaltyNs_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_penaltyNs_1222_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1223_ = lean_box(v_penaltyNs_1222_);
v___x_1224_ = lean_box(v_penaltyNs_1222_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1(void){
_start:
{
lean_object* v___x_1226_; lean_object* v_lastSepIdx_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
v_lastSepIdx_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_lastSepIdx_1227_);
lean_ctor_set(v___x_1228_, 1, v___x_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(lean_object* v_pattern_1229_, lean_object* v_word_1230_, lean_object* v_patternRoles_1231_, lean_object* v_wordRoles_1232_){
_start:
{
uint16_t v___y_1234_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_lastSepIdx_1245_; uint16_t v_penaltyNs_1246_; lean_object* v___x_1247_; lean_object* v_runLengths_1248_; lean_object* v___x_1249_; lean_object* v_startPenalties_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_snd_1256_; lean_object* v_fst_1257_; lean_object* v_fst_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1288_; 
v___x_1240_ = lean_string_length(v_pattern_1229_);
v___x_1241_ = lean_string_length(v_word_1230_);
v___x_1242_ = lean_nat_mul(v___x_1240_, v___x_1241_);
v___x_1243_ = lean_unsigned_to_nat(2u);
v___x_1244_ = lean_nat_mul(v___x_1242_, v___x_1243_);
v_lastSepIdx_1245_ = lean_unsigned_to_nat(0u);
v_penaltyNs_1246_ = lean_uint16_once(&l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0, &l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once, _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0);
v___x_1247_ = lean_box(v_penaltyNs_1246_);
v_runLengths_1248_ = lean_mk_array(v___x_1242_, v___x_1247_);
v___x_1249_ = lean_box(v_penaltyNs_1246_);
v_startPenalties_1250_ = lean_mk_array(v___x_1241_, v___x_1249_);
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1252_, 0, v_lastSepIdx_1245_);
lean_ctor_set(v___x_1252_, 1, v___x_1241_);
lean_ctor_set(v___x_1252_, 2, v___x_1251_);
v___x_1253_ = lean_obj_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_startPenalties_1250_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1232_, v___x_1252_, v___x_1254_, v_lastSepIdx_1245_);
lean_dec_ref_known(v___x_1252_, 3);
v_snd_1256_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_snd_1256_);
v_fst_1257_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_fst_1257_);
lean_dec_ref(v___x_1255_);
v_fst_1258_ = lean_ctor_get(v_snd_1256_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_snd_1256_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_snd_1256_, 1);
lean_dec(v_unused_1289_);
v___x_1260_ = v_snd_1256_;
v_isShared_1261_ = v_isSharedCheck_1288_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_fst_1258_);
lean_dec(v_snd_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1288_;
goto v_resetjp_1259_;
}
v___jp_1233_:
{
uint16_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1236_ = lean_int16_dec_le(v___y_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_int16_to_int(v___y_1234_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_box(0);
return v___x_1239_;
}
}
v_resetjp_1259_:
{
uint16_t v_matchScore_1262_; lean_object* v___x_1263_; lean_object* v_result_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v_matchScore_1262_ = lean_uint16_once(&l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1, &l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once, _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
v___x_1263_ = lean_box(v_matchScore_1262_);
v_result_1264_ = lean_mk_array(v___x_1244_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1265_, 0, v_lastSepIdx_1245_);
lean_ctor_set(v___x_1265_, 1, v___x_1240_);
lean_ctor_set(v___x_1265_, 2, v___x_1251_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v_runLengths_1248_);
lean_ctor_set(v___x_1260_, 0, v_result_1264_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_result_1264_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_runLengths_1248_);
v___x_1267_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v_fst_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint16_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint16_t v___x_1282_; uint16_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1268_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1230_, v_pattern_1229_, v_patternRoles_1231_, v_wordRoles_1232_, v_fst_1257_, v_fst_1258_, v___x_1240_, v___x_1241_, v___x_1265_, v___x_1267_, v_lastSepIdx_1245_);
lean_dec_ref_known(v___x_1265_, 3);
lean_dec(v_fst_1258_);
lean_dec(v_fst_1257_);
v_fst_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_fst_1269_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = lean_nat_sub(v___x_1240_, v___x_1251_);
v___x_1271_ = lean_nat_sub(v___x_1241_, v___x_1251_);
v___x_1272_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
v___x_1273_ = lean_nat_mul(v___x_1270_, v___x_1241_);
lean_dec(v___x_1270_);
v___x_1274_ = lean_nat_mul(v___x_1273_, v___x_1243_);
lean_dec(v___x_1273_);
v___x_1275_ = lean_nat_mul(v___x_1271_, v___x_1243_);
lean_dec(v___x_1271_);
v___x_1276_ = lean_nat_add(v___x_1274_, v___x_1275_);
lean_dec(v___x_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(v___x_1272_);
v___x_1278_ = lean_array_get(v___x_1277_, v_fst_1269_, v___x_1276_);
lean_dec(v___x_1277_);
v___x_1279_ = lean_nat_add(v___x_1276_, v___x_1251_);
lean_dec(v___x_1276_);
v___x_1280_ = lean_box(v___x_1272_);
v___x_1281_ = lean_array_get(v___x_1280_, v_fst_1269_, v___x_1279_);
lean_dec(v___x_1279_);
lean_dec(v_fst_1269_);
lean_dec(v___x_1280_);
v___x_1282_ = lean_unbox(v___x_1278_);
v___x_1283_ = lean_unbox(v___x_1281_);
v___x_1284_ = lean_int16_dec_le(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
uint16_t v___x_1285_; 
lean_dec(v___x_1281_);
v___x_1285_ = lean_unbox(v___x_1278_);
lean_dec(v___x_1278_);
v___y_1234_ = v___x_1285_;
goto v___jp_1233_;
}
else
{
uint16_t v___x_1286_; 
lean_dec(v___x_1278_);
v___x_1286_ = lean_unbox(v___x_1281_);
lean_dec(v___x_1281_);
v___y_1234_ = v___x_1286_;
goto v___jp_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(lean_object* v_pattern_1290_, lean_object* v_word_1291_, lean_object* v_patternRoles_1292_, lean_object* v_wordRoles_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1290_, v_word_1291_, v_patternRoles_1292_, v_wordRoles_1293_);
lean_dec_ref(v_wordRoles_1293_);
lean_dec_ref(v_patternRoles_1292_);
lean_dec_ref(v_word_1291_);
lean_dec_ref(v_pattern_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(lean_object* v_wordRoles_1295_, lean_object* v_range_1296_, lean_object* v_b_1297_, lean_object* v_i_1298_, lean_object* v_hs_1299_, lean_object* v_hl_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_1295_, v_range_1296_, v_b_1297_, v_i_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(lean_object* v_wordRoles_1302_, lean_object* v_range_1303_, lean_object* v_b_1304_, lean_object* v_i_1305_, lean_object* v_hs_1306_, lean_object* v_hl_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_1302_, v_range_1303_, v_b_1304_, v_i_1305_, v_hs_1306_, v_hl_1307_);
lean_dec_ref(v_range_1303_);
lean_dec_ref(v_wordRoles_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(lean_object* v_word_1309_, lean_object* v_a_1310_, lean_object* v_pattern_1311_, lean_object* v_patternRoles_1312_, lean_object* v_wordRoles_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v_range_1316_, lean_object* v_b_1317_, lean_object* v_i_1318_, lean_object* v_hs_1319_, lean_object* v_hl_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_1309_, v_a_1310_, v_pattern_1311_, v_patternRoles_1312_, v_wordRoles_1313_, v___x_1314_, v___x_1315_, v_range_1316_, v_b_1317_, v_i_1318_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(lean_object* v_word_1322_, lean_object* v_a_1323_, lean_object* v_pattern_1324_, lean_object* v_patternRoles_1325_, lean_object* v_wordRoles_1326_, lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_range_1329_, lean_object* v_b_1330_, lean_object* v_i_1331_, lean_object* v_hs_1332_, lean_object* v_hl_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v_word_1322_, v_a_1323_, v_pattern_1324_, v_patternRoles_1325_, v_wordRoles_1326_, v___x_1327_, v___x_1328_, v_range_1329_, v_b_1330_, v_i_1331_, v_hs_1332_, v_hl_1333_);
lean_dec_ref(v_range_1329_);
lean_dec(v___x_1328_);
lean_dec_ref(v___x_1327_);
lean_dec_ref(v_wordRoles_1326_);
lean_dec_ref(v_patternRoles_1325_);
lean_dec_ref(v_pattern_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_word_1322_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(lean_object* v_word_1335_, lean_object* v_pattern_1336_, lean_object* v_patternRoles_1337_, lean_object* v_wordRoles_1338_, lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v_range_1343_, lean_object* v_b_1344_, lean_object* v_i_1345_, lean_object* v_hs_1346_, lean_object* v_hl_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_1335_, v_pattern_1336_, v_patternRoles_1337_, v_wordRoles_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v_range_1343_, v_b_1344_, v_i_1345_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(lean_object* v_word_1349_, lean_object* v_pattern_1350_, lean_object* v_patternRoles_1351_, lean_object* v_wordRoles_1352_, lean_object* v___x_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v_range_1357_, lean_object* v_b_1358_, lean_object* v_i_1359_, lean_object* v_hs_1360_, lean_object* v_hl_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v_word_1349_, v_pattern_1350_, v_patternRoles_1351_, v_wordRoles_1352_, v___x_1353_, v___x_1354_, v___x_1355_, v___x_1356_, v_range_1357_, v_b_1358_, v_i_1359_, v_hs_1360_, v_hl_1361_);
lean_dec_ref(v_range_1357_);
lean_dec(v___x_1356_);
lean_dec(v___x_1355_);
lean_dec(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v_wordRoles_1352_);
lean_dec_ref(v_patternRoles_1351_);
lean_dec_ref(v_pattern_1350_);
lean_dec_ref(v_word_1349_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v_word_1365_, lean_object* v_pattern_1366_, lean_object* v_patternRoles_1367_, lean_object* v_wordRoles_1368_, lean_object* v___x_1369_, lean_object* v___x_1370_, lean_object* v_range_1371_, lean_object* v_b_1372_, lean_object* v_i_1373_, lean_object* v_hs_1374_, lean_object* v_hl_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_1363_, v___x_1364_, v_word_1365_, v_pattern_1366_, v_patternRoles_1367_, v_wordRoles_1368_, v___x_1369_, v___x_1370_, v_range_1371_, v_b_1372_, v_i_1373_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v_word_1379_, lean_object* v_pattern_1380_, lean_object* v_patternRoles_1381_, lean_object* v_wordRoles_1382_, lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v_range_1385_, lean_object* v_b_1386_, lean_object* v_i_1387_, lean_object* v_hs_1388_, lean_object* v_hl_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(v___x_1377_, v___x_1378_, v_word_1379_, v_pattern_1380_, v_patternRoles_1381_, v_wordRoles_1382_, v___x_1383_, v___x_1384_, v_range_1385_, v_b_1386_, v_i_1387_, v_hs_1388_, v_hl_1389_);
lean_dec_ref(v_range_1385_);
lean_dec(v___x_1384_);
lean_dec_ref(v___x_1383_);
lean_dec_ref(v_wordRoles_1382_);
lean_dec_ref(v_patternRoles_1381_);
lean_dec_ref(v_pattern_1380_);
lean_dec_ref(v_word_1379_);
lean_dec(v___x_1378_);
lean_dec(v___x_1377_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(lean_object* v_a_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_nat_to_int(v_a_1391_);
return v___x_1392_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1393_; double v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_float_of_nat(v___x_1393_);
return v___x_1394_;
}
}
static double _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1(void){
_start:
{
lean_object* v___x_1395_; double v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_float_of_nat(v___x_1395_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(2u);
v___x_1398_ = lean_nat_to_int(v___x_1397_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1(void){
_start:
{
double v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1400_ = lean_box_float(v___x_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(lean_object* v_pattern_1403_, lean_object* v_word_1404_){
_start:
{
double v___y_1406_; double v___y_1407_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = lean_string_utf8_byte_size(v_pattern_1403_);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_nat_dec_eq(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_score_1419_; uint8_t v___x_1435_; 
v___x_1416_ = lean_string_length(v_word_1404_);
v___x_1417_ = lean_string_length(v_pattern_1403_);
v___x_1435_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = l_String_charactersIn(v_pattern_1403_, v_word_1404_);
v___x_1437_ = lean_bool_not(v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_1403_);
v___x_1439_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_1404_);
v___x_1440_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_1403_, v_word_1404_, v___x_1438_, v___x_1439_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v___x_1438_);
if (lean_obj_tag(v___x_1440_) == 1)
{
lean_object* v_val_1441_; uint8_t v___x_1442_; 
v_val_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_nat_dec_eq(v___x_1417_, v___x_1416_);
if (v___x_1442_ == 0)
{
v_score_1419_ = v_val_1441_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1443_; lean_object* v_score_1444_; 
v___x_1443_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
v_score_1444_ = lean_int_mul(v_val_1441_, v___x_1443_);
lean_dec(v_val_1441_);
v_score_1419_ = v_score_1444_;
goto v___jp_1418_;
}
}
else
{
lean_object* v___x_1445_; 
lean_dec(v___x_1440_);
v___x_1445_ = lean_box(0);
return v___x_1445_;
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_box(0);
return v___x_1446_;
}
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_box(0);
return v___x_1447_;
}
v___jp_1418_:
{
lean_object* v_perfect_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_perfectMatch_1427_; double v___x_1428_; lean_object* v___x_1429_; double v___x_1430_; double v_normScore_1431_; double v___x_1432_; double v___x_1433_; uint8_t v___x_1434_; 
v_perfect_1420_ = lean_unsigned_to_nat(4u);
v___x_1421_ = lean_nat_mul(v_perfect_1420_, v___x_1417_);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v___x_1417_, v___x_1422_);
v___x_1424_ = lean_nat_mul(v___x_1417_, v___x_1423_);
lean_dec(v___x_1423_);
v___x_1425_ = lean_nat_shiftr(v___x_1424_, v___x_1422_);
lean_dec(v___x_1424_);
v___x_1426_ = lean_nat_sub(v___x_1425_, v___x_1422_);
lean_dec(v___x_1425_);
v_perfectMatch_1427_ = lean_nat_add(v___x_1421_, v___x_1426_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
v___x_1428_ = l_Float_ofInt(v_score_1419_);
lean_dec(v_score_1419_);
v___x_1429_ = lean_nat_to_int(v_perfectMatch_1427_);
v___x_1430_ = l_Float_ofInt(v___x_1429_);
lean_dec(v___x_1429_);
v_normScore_1431_ = lean_float_div(v___x_1428_, v___x_1430_);
v___x_1432_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0);
v___x_1433_ = lean_float_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1);
v___x_1434_ = lean_float_decLe(v___x_1433_, v_normScore_1431_);
if (v___x_1434_ == 0)
{
v___y_1406_ = v___x_1432_;
v___y_1407_ = v___x_1433_;
goto v___jp_1405_;
}
else
{
v___y_1406_ = v___x_1432_;
v___y_1407_ = v_normScore_1431_;
goto v___jp_1405_;
}
}
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_obj_once(&l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3, &l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once, _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3);
return v___x_1448_;
}
v___jp_1405_:
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_float_decLe(v___y_1406_, v___y_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_box_float(v___y_1407_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_box_float(v___y_1406_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(lean_object* v_pattern_1449_, lean_object* v_word_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1449_, v_word_1450_);
lean_dec_ref(v_word_1450_);
lean_dec_ref(v_pattern_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object* v_pattern_1452_, lean_object* v_word_1453_, double v_threshold_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_1452_, v_word_1453_);
if (lean_obj_tag(v___x_1455_) == 0)
{
return v___x_1455_;
}
else
{
lean_object* v_val_1456_; double v___x_1457_; uint8_t v___x_1458_; 
v_val_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1456_);
v___x_1457_ = lean_unbox_float(v_val_1456_);
lean_dec(v_val_1456_);
v___x_1458_ = lean_float_decLt(v_threshold_1454_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref_known(v___x_1455_, 1);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(lean_object* v_pattern_1460_, lean_object* v_word_1461_, lean_object* v_threshold_1462_){
_start:
{
double v_threshold_boxed_1463_; lean_object* v_res_1464_; 
v_threshold_boxed_1463_ = lean_unbox_float(v_threshold_1462_);
lean_dec_ref(v_threshold_1462_);
v_res_1464_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1460_, v_word_1461_, v_threshold_boxed_1463_);
lean_dec_ref(v_word_1461_);
lean_dec_ref(v_pattern_1460_);
return v_res_1464_;
}
}
LEAN_EXPORT uint8_t l_Lean_FuzzyMatching_fuzzyMatch(lean_object* v_pattern_1465_, lean_object* v_word_1466_, double v_threshold_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(v_pattern_1465_, v_word_1466_, v_threshold_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
uint8_t v___x_1469_; 
v___x_1469_ = 0;
return v___x_1469_;
}
else
{
uint8_t v___x_1470_; 
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = 1;
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FuzzyMatching_fuzzyMatch___boxed(lean_object* v_pattern_1471_, lean_object* v_word_1472_, lean_object* v_threshold_1473_){
_start:
{
double v_threshold_boxed_1474_; uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_threshold_boxed_1474_ = lean_unbox_float(v_threshold_1473_);
lean_dec_ref(v_threshold_1473_);
v_res_1475_ = l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_1471_, v_word_1472_, v_threshold_boxed_1474_);
lean_dec_ref(v_word_1472_);
lean_dec_ref(v_pattern_1471_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
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
