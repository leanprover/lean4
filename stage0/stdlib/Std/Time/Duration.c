// Lean compiler output
// Module: Std.Time.Duration
// Imports: public import Std.Time.Date public import Init.Data.String.Basic
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Std_Time_Internal_UnitVal_instToString___lam__0(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object*);
lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Time_Hour_Offset_toSeconds___boxed(lean_object*);
lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object*);
extern lean_object* l_Std_Time_Nanosecond_instOrdSpan;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Minute_Offset_toSeconds___boxed(lean_object*);
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprDuration_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprDuration_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nano"};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Time_instReprDuration_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__12;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__14 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__14_value;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Time_instReprDuration_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__17_value;
static lean_once_cell_t l_Std_Time_instReprDuration_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__18;
static lean_once_cell_t l_Std_Time_instReprDuration_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__19;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__20 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Time_instReprDuration_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__17_value)}};
static const lean_object* l_Std_Time_instReprDuration_repr___redArg___closed__21 = (const lean_object*)&l_Std_Time_instReprDuration_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprDuration_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprDuration___closed__0 = (const lean_object*)&l_Std_Time_instReprDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprDuration = (const lean_object*)&l_Std_Time_instReprDuration___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqDuration_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instToStringDuration_leftPad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_instToStringDuration_leftPad___closed__0 = (const lean_object*)&l_Std_Time_instToStringDuration_leftPad___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration_leftPad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration_leftPad___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instToStringDuration___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Std_Time_instToStringDuration___lam__0___closed__0 = (const lean_object*)&l_Std_Time_instToStringDuration___lam__0___closed__0_value;
static lean_once_cell_t l_Std_Time_instToStringDuration___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instToStringDuration___lam__0___closed__1;
static const lean_string_object l_Std_Time_instToStringDuration___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Time_instToStringDuration___lam__0___closed__2 = (const lean_object*)&l_Std_Time_instToStringDuration___lam__0___closed__2_value;
static const lean_string_object l_Std_Time_instToStringDuration___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_instToStringDuration___lam__0___closed__3 = (const lean_object*)&l_Std_Time_instToStringDuration___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_instToStringDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instToStringDuration___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instToStringDuration___closed__0 = (const lean_object*)&l_Std_Time_instToStringDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instToStringDuration = (const lean_object*)&l_Std_Time_instToStringDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprDuration__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprDuration__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprDuration__1___closed__0 = (const lean_object*)&l_Std_Time_instReprDuration__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprDuration__1 = (const lean_object*)&l_Std_Time_instReprDuration__1___closed__0_value;
static lean_once_cell_t l_Std_Time_instInhabitedDuration___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedDuration___closed__0;
static lean_once_cell_t l_Std_Time_instInhabitedDuration___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedDuration___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDuration;
LEAN_EXPORT lean_object* l_Std_Time_instOfNatDuration(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdDuration___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdDuration___closed__0 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__0_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdDuration___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdDuration___closed__1 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__1_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdDuration___closed__2 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__2_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdDuration___closed__2_value),((lean_object*)&l_Std_Time_instOrdDuration___closed__0_value)} };
static const lean_object* l_Std_Time_instOrdDuration___closed__3 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__3_value;
static lean_once_cell_t l_Std_Time_instOrdDuration___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdDuration___closed__4;
static lean_once_cell_t l_Std_Time_instOrdDuration___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdDuration___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration;
LEAN_EXPORT lean_object* l_Std_Time_Duration_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Duration_ofNanoseconds_spec__1(lean_object*);
static lean_once_cell_t l_Std_Time_Duration_ofNanoseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_ofNanoseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Duration_ofNanoseconds_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Duration_ofMillisecond___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_ofMillisecond___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Duration_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_isZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Duration_toMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_toMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instLE;
LEAN_EXPORT uint8_t l_Std_Time_Duration_instDecidableLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instLT;
LEAN_EXPORT uint8_t l_Std_Time_Duration_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLt___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Duration_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Duration_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Duration_subSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_subSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Duration_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Duration_addWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Duration_addWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Duration_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset = (const lean_object*)&l_Std_Time_Duration_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset = (const lean_object*)&l_Std_Time_Duration_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset__1 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset__1 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset__2 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset__2 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset__3 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset__3 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset__4 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset__4 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAddOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset__5___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset__5 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset__5___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset__5 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAddOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddOffset__6___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddOffset__6 = (const lean_object*)&l_Std_Time_Duration_instHAddOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSubOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubOffset__6___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubOffset__6 = (const lean_object*)&l_Std_Time_Duration_instHSubOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSub___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSub = (const lean_object*)&l_Std_Time_Duration_instHSub___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instHAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAdd___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAdd = (const lean_object*)&l_Std_Time_Duration_instHAdd___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_ofNanoseconds___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instCoeOffset___closed__0 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instCoeOffset = (const lean_object*)&l_Std_Time_Duration_instCoeOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_ofSeconds, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__1___closed__0 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instCoeOffset__1 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Minute_Offset_toSeconds___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__2___closed__0 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Duration_instCoeOffset__1___closed__0_value),((lean_object*)&l_Std_Time_Duration_instCoeOffset__2___closed__0_value)} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__2___closed__1 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__2___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instCoeOffset__2 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__2___closed__1_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Hour_Offset_toSeconds___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__3___closed__0 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Duration_instCoeOffset__1___closed__0_value),((lean_object*)&l_Std_Time_Duration_instCoeOffset__3___closed__0_value)} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__3___closed__1 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__3___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instCoeOffset__3 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__3___closed__1_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_Offset_toSeconds___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__4___closed__0 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_Offset_toDays___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__4___closed__1 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__1_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__0_value),((lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__1_value)} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__4___closed__2 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__2_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Duration_instCoeOffset__1___closed__0_value),((lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__2_value)} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__4___closed__3 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__3_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instCoeOffset__4 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__3_value;
static const lean_closure_object l_Std_Time_Duration_instCoeOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Duration_instCoeOffset__1___closed__0_value),((lean_object*)&l_Std_Time_Duration_instCoeOffset__4___closed__0_value)} };
static const lean_object* l_Std_Time_Duration_instCoeOffset__5___closed__0 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instCoeOffset__5 = (const lean_object*)&l_Std_Time_Duration_instCoeOffset__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Duration_instHMulInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_instHMulInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHMulInt___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHMulInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHMulInt = (const lean_object*)&l_Std_Time_Duration_instHMulInt___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Duration_instHMulInt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_instHMulInt__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHMulInt__1___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHMulInt__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHMulInt__1 = (const lean_object*)&l_Std_Time_Duration_instHMulInt__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Duration_instHAddPlainTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHAddPlainTime___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHAddPlainTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHAddPlainTime = (const lean_object*)&l_Std_Time_Duration_instHAddPlainTime___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Duration_instHSubPlainTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Duration_instHSubPlainTime___closed__0 = (const lean_object*)&l_Std_Time_Duration_instHSubPlainTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Duration_instHSubPlainTime = (const lean_object*)&l_Std_Time_Duration_instHSubPlainTime___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprDuration_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instReprDuration_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(10u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_instReprDuration_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(8u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_Time_instReprDuration_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__0));
v___x_34_ = lean_string_length(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_Time_instReprDuration_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_obj_once(&l_Std_Time_instReprDuration_repr___redArg___closed__18, &l_Std_Time_instReprDuration_repr___redArg___closed__18_once, _init_l_Std_Time_instReprDuration_repr___redArg___closed__18);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration_repr___redArg(lean_object* v_x_41_){
_start:
{
lean_object* v_second_42_; lean_object* v_nano_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_84_; 
v_second_42_ = lean_ctor_get(v_x_41_, 0);
v_nano_43_ = lean_ctor_get(v_x_41_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_84_ == 0)
{
v___x_45_ = v_x_41_;
v_isShared_46_ = v_isSharedCheck_84_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_nano_43_);
lean_inc(v_second_42_);
lean_dec(v_x_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_84_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_47_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__5));
v___x_48_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__6));
v___x_49_ = lean_obj_once(&l_Std_Time_instReprDuration_repr___redArg___closed__7, &l_Std_Time_instReprDuration_repr___redArg___closed__7_once, _init_l_Std_Time_instReprDuration_repr___redArg___closed__7);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = l_Std_Time_Internal_UnitVal_instRepr___lam__0(v_second_42_, v___x_50_);
lean_dec(v_second_42_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 4);
lean_ctor_set(v___x_45_, 1, v___x_51_);
lean_ctor_set(v___x_45_, 0, v___x_49_);
v___x_53_ = v___x_45_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_51_);
v___x_53_ = v_reuseFailAlloc_83_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_54_ = 0;
v___x_55_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*1, v___x_54_);
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_48_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__9));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_box(1);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__11));
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_47_);
v___x_64_ = lean_obj_once(&l_Std_Time_instReprDuration_repr___redArg___closed__12, &l_Std_Time_instReprDuration_repr___redArg___closed__12_once, _init_l_Std_Time_instReprDuration_repr___redArg___closed__12);
v___x_65_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_nano_43_, v___x_50_);
lean_dec(v_nano_43_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*1, v___x_54_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_63_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_57_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_59_);
v___x_71_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__14));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_47_);
v___x_74_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__16));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l_Std_Time_instReprDuration_repr___redArg___closed__19, &l_Std_Time_instReprDuration_repr___redArg___closed__19_once, _init_l_Std_Time_instReprDuration_repr___redArg___closed__19);
v___x_77_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__20));
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_75_);
v___x_79_ = ((lean_object*)(l_Std_Time_instReprDuration_repr___redArg___closed__21));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_76_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_54_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration_repr(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_Time_instReprDuration_repr___redArg(v_x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration_repr___boxed(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Time_instReprDuration_repr(v_x_88_, v_prec_89_);
lean_dec(v_prec_89_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_second_95_; lean_object* v_nano_96_; lean_object* v_second_97_; lean_object* v_nano_98_; uint8_t v___x_99_; 
v_second_95_ = lean_ctor_get(v_x_93_, 0);
v_nano_96_ = lean_ctor_get(v_x_93_, 1);
v_second_97_ = lean_ctor_get(v_x_94_, 0);
v_nano_98_ = lean_ctor_get(v_x_94_, 1);
v___x_99_ = lean_int_dec_eq(v_second_95_, v_second_97_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = lean_int_dec_eq(v_nano_96_, v_nano_98_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqDuration_decEq___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqDuration(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqDuration___boxed(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Time_instDecidableEqDuration(v_x_108_, v_x_109_);
lean_dec_ref(v_x_109_);
lean_dec_ref(v_x_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_zero_114_; uint8_t v_isZero_115_; 
v_zero_114_ = lean_unsigned_to_nat(0u);
v_isZero_115_ = lean_nat_dec_eq(v_x_112_, v_zero_114_);
if (v_isZero_115_ == 1)
{
lean_dec(v_x_112_);
return v_x_113_;
}
else
{
uint32_t v___x_116_; lean_object* v_one_117_; lean_object* v_n_118_; lean_object* v___x_119_; 
v___x_116_ = 48;
v_one_117_ = lean_unsigned_to_nat(1u);
v_n_118_ = lean_nat_sub(v_x_112_, v_one_117_);
lean_dec(v_x_112_);
v___x_119_ = lean_string_push(v_x_113_, v___x_116_);
v_x_112_ = v_n_118_;
v_x_113_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration_leftPad(lean_object* v_n_122_, lean_object* v_s_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___x_125_ = lean_string_length(v_s_123_);
v___x_126_ = lean_nat_sub(v_n_122_, v___x_125_);
v___x_127_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(v___x_126_, v___x_124_);
v___x_128_ = lean_string_append(v___x_127_, v_s_123_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration_leftPad___boxed(lean_object* v_n_129_, lean_object* v_s_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Time_instToStringDuration_leftPad(v_n_129_, v_s_130_);
lean_dec_ref(v_s_130_);
lean_dec(v_n_129_);
return v_res_131_;
}
}
static lean_object* _init_l_Std_Time_instToStringDuration___lam__0___closed__1(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration___lam__0(lean_object* v_s_137_){
_start:
{
lean_object* v___y_139_; lean_object* v___y_140_; lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v_second_151_; lean_object* v_nano_152_; lean_object* v_fst_154_; lean_object* v_fst_155_; lean_object* v_snd_156_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_second_151_ = lean_ctor_get(v_s_137_, 0);
lean_inc(v_second_151_);
v_nano_152_ = lean_ctor_get(v_s_137_, 1);
lean_inc(v_nano_152_);
lean_dec_ref(v_s_137_);
v___x_174_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_175_ = lean_int_dec_lt(v___x_174_, v_second_151_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_int_dec_lt(v_second_151_, v___x_174_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = lean_int_dec_lt(v_nano_152_, v___x_174_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_152_);
v_fst_154_ = v___x_178_;
v_fst_155_ = v_second_151_;
v_snd_156_ = v_nano_152_;
goto v___jp_153_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_180_ = lean_int_neg(v_second_151_);
lean_dec(v_second_151_);
v___x_181_ = lean_int_neg(v_nano_152_);
v_fst_154_ = v___x_179_;
v_fst_155_ = v___x_180_;
v_snd_156_ = v___x_181_;
goto v___jp_153_;
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_183_ = lean_int_neg(v_second_151_);
lean_dec(v_second_151_);
v___x_184_ = lean_int_neg(v_nano_152_);
v_fst_154_ = v___x_182_;
v_fst_155_ = v___x_183_;
v_snd_156_ = v___x_184_;
goto v___jp_153_;
}
}
else
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_152_);
v_fst_154_ = v___x_185_;
v_fst_155_ = v_second_151_;
v_snd_156_ = v_nano_152_;
goto v___jp_153_;
}
v___jp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_string_append(v___y_139_, v___y_140_);
lean_dec_ref(v___y_140_);
v___x_142_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__0));
v___x_143_ = lean_string_append(v___x_141_, v___x_142_);
return v___x_143_;
}
v___jp_144_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_Std_Time_instToStringDuration_leftPad(v___y_147_, v___y_148_);
lean_dec_ref(v___y_148_);
v___x_150_ = lean_string_append(v___y_145_, v___x_149_);
lean_dec_ref(v___x_149_);
v___y_139_ = v___y_146_;
v___y_140_ = v___x_150_;
goto v___jp_138_;
}
v___jp_153_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_157_ = l_Std_Time_Internal_UnitVal_instToString___lam__0(v_fst_155_);
lean_dec(v_fst_155_);
v___x_158_ = lean_string_append(v_fst_154_, v___x_157_);
lean_dec_ref(v___x_157_);
v___x_159_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_160_ = lean_int_dec_eq(v_nano_152_, v___x_159_);
lean_dec(v_nano_152_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v_isNeg_163_; 
v___x_161_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__2));
v___x_162_ = lean_unsigned_to_nat(9u);
v_isNeg_163_ = lean_int_dec_lt(v_snd_156_, v___x_159_);
if (v_isNeg_163_ == 0)
{
lean_object* v_a_164_; lean_object* v___x_165_; 
v_a_164_ = lean_nat_abs(v_snd_156_);
lean_dec(v_snd_156_);
v___x_165_ = l_Nat_reprFast(v_a_164_);
v___y_145_ = v___x_161_;
v___y_146_ = v___x_158_;
v___y_147_ = v___x_162_;
v___y_148_ = v___x_165_;
goto v___jp_144_;
}
else
{
lean_object* v_abs_166_; lean_object* v_one_167_; lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_abs_166_ = lean_nat_abs(v_snd_156_);
lean_dec(v_snd_156_);
v_one_167_ = lean_unsigned_to_nat(1u);
v_a_168_ = lean_nat_sub(v_abs_166_, v_one_167_);
lean_dec(v_abs_166_);
v___x_169_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_170_ = lean_nat_add(v_a_168_, v_one_167_);
lean_dec(v_a_168_);
v___x_171_ = l_Nat_reprFast(v___x_170_);
v___x_172_ = lean_string_append(v___x_169_, v___x_171_);
lean_dec_ref(v___x_171_);
v___y_145_ = v___x_161_;
v___y_146_ = v___x_158_;
v___y_147_ = v___x_162_;
v___y_148_ = v___x_172_;
goto v___jp_144_;
}
}
else
{
lean_object* v___x_173_; 
lean_dec(v_snd_156_);
v___x_173_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___y_139_ = v___x_158_;
v___y_140_ = v___x_173_;
goto v___jp_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0(lean_object* v_s_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v_second_205_; lean_object* v_nano_206_; lean_object* v_fst_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_second_205_ = lean_ctor_get(v_s_188_, 0);
lean_inc(v_second_205_);
v_nano_206_ = lean_ctor_get(v_s_188_, 1);
lean_inc(v_nano_206_);
lean_dec_ref(v_s_188_);
v___x_228_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_229_ = lean_int_dec_lt(v___x_228_, v_second_205_);
if (v___x_229_ == 0)
{
uint8_t v___x_230_; 
v___x_230_ = lean_int_dec_lt(v_second_205_, v___x_228_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
v___x_231_ = lean_int_dec_lt(v_nano_206_, v___x_228_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
v___x_232_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_206_);
v_fst_208_ = v___x_232_;
v_fst_209_ = v_second_205_;
v_snd_210_ = v_nano_206_;
goto v___jp_207_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_234_ = lean_int_neg(v_second_205_);
lean_dec(v_second_205_);
v___x_235_ = lean_int_neg(v_nano_206_);
v_fst_208_ = v___x_233_;
v_fst_209_ = v___x_234_;
v_snd_210_ = v___x_235_;
goto v___jp_207_;
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_237_ = lean_int_neg(v_second_205_);
lean_dec(v_second_205_);
v___x_238_ = lean_int_neg(v_nano_206_);
v_fst_208_ = v___x_236_;
v_fst_209_ = v___x_237_;
v_snd_210_ = v___x_238_;
goto v___jp_207_;
}
}
else
{
lean_object* v___x_239_; 
v___x_239_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_206_);
v_fst_208_ = v___x_239_;
v_fst_209_ = v_second_205_;
v_snd_210_ = v_nano_206_;
goto v___jp_207_;
}
v___jp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = lean_string_append(v___y_191_, v___y_192_);
lean_dec_ref(v___y_192_);
v___x_194_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__0));
v___x_195_ = lean_string_append(v___x_193_, v___x_194_);
v___x_196_ = l_String_quote(v___x_195_);
v___x_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
v___jp_198_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = l_Std_Time_instToStringDuration_leftPad(v___y_200_, v___y_202_);
lean_dec_ref(v___y_202_);
v___x_204_ = lean_string_append(v___y_201_, v___x_203_);
lean_dec_ref(v___x_203_);
v___y_191_ = v___y_199_;
v___y_192_ = v___x_204_;
goto v___jp_190_;
}
v___jp_207_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_211_ = l_Std_Time_Internal_UnitVal_instToString___lam__0(v_fst_209_);
lean_dec(v_fst_209_);
v___x_212_ = lean_string_append(v_fst_208_, v___x_211_);
lean_dec_ref(v___x_211_);
v___x_213_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_214_ = lean_int_dec_eq(v_nano_206_, v___x_213_);
lean_dec(v_nano_206_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v_isNeg_217_; 
v___x_215_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__2));
v___x_216_ = lean_unsigned_to_nat(9u);
v_isNeg_217_ = lean_int_dec_lt(v_snd_210_, v___x_213_);
if (v_isNeg_217_ == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; 
v_a_218_ = lean_nat_abs(v_snd_210_);
lean_dec(v_snd_210_);
v___x_219_ = l_Nat_reprFast(v_a_218_);
v___y_199_ = v___x_212_;
v___y_200_ = v___x_216_;
v___y_201_ = v___x_215_;
v___y_202_ = v___x_219_;
goto v___jp_198_;
}
else
{
lean_object* v_abs_220_; lean_object* v_one_221_; lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_abs_220_ = lean_nat_abs(v_snd_210_);
lean_dec(v_snd_210_);
v_one_221_ = lean_unsigned_to_nat(1u);
v_a_222_ = lean_nat_sub(v_abs_220_, v_one_221_);
lean_dec(v_abs_220_);
v___x_223_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_224_ = lean_nat_add(v_a_222_, v_one_221_);
lean_dec(v_a_222_);
v___x_225_ = l_Nat_reprFast(v___x_224_);
v___x_226_ = lean_string_append(v___x_223_, v___x_225_);
lean_dec_ref(v___x_225_);
v___y_199_ = v___x_212_;
v___y_200_ = v___x_216_;
v___y_201_ = v___x_215_;
v___y_202_ = v___x_226_;
goto v___jp_198_;
}
}
else
{
lean_object* v___x_227_; 
lean_dec(v_snd_210_);
v___x_227_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___y_191_ = v___x_212_;
v___y_192_ = v___x_227_;
goto v___jp_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0___boxed(lean_object* v_s_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Time_instReprDuration__1___lam__0(v_s_240_, v___y_241_);
lean_dec(v___y_241_);
return v_res_242_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration___closed__0(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_to_int(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration___closed__1(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Std_Time_instInhabitedDuration___closed__0, &l_Std_Time_instInhabitedDuration___closed__0_once, _init_l_Std_Time_instInhabitedDuration___closed__0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&l_Std_Time_instInhabitedDuration___closed__1, &l_Std_Time_instInhabitedDuration___closed__1_once, _init_l_Std_Time_instInhabitedDuration___closed__1);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOfNatDuration(lean_object* v_n_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_nat_to_int(v_n_250_);
v___x_252_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0(lean_object* v_x_254_){
_start:
{
lean_object* v_second_255_; 
v_second_255_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_second_255_);
return v_second_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0___boxed(lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Time_instOrdDuration___lam__0(v_x_256_);
lean_dec_ref(v_x_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1(lean_object* v_x_258_){
_start:
{
lean_object* v_nano_259_; 
v_nano_259_ = lean_ctor_get(v_x_258_, 1);
lean_inc(v_nano_259_);
return v_nano_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1___boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Time_instOrdDuration___lam__1(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
static lean_object* _init_l_Std_Time_instOrdDuration___closed__4(void){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___f_268_ = ((lean_object*)(l_Std_Time_instOrdDuration___closed__1));
v___x_269_ = l_Std_Time_Nanosecond_instOrdSpan;
v___x_270_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_270_, 0, lean_box(0));
lean_closure_set(v___x_270_, 1, lean_box(0));
lean_closure_set(v___x_270_, 2, v___x_269_);
lean_closure_set(v___x_270_, 3, v___f_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Std_Time_instOrdDuration___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Std_Time_instOrdDuration___closed__4, &l_Std_Time_instOrdDuration___closed__4_once, _init_l_Std_Time_instOrdDuration___closed__4);
v___x_272_ = ((lean_object*)(l_Std_Time_instOrdDuration___closed__3));
v___x_273_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_273_, 0, lean_box(0));
lean_closure_set(v___x_273_, 1, lean_box(0));
lean_closure_set(v___x_273_, 2, v___x_272_);
lean_closure_set(v___x_273_, 3, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Std_Time_instOrdDuration(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Std_Time_instOrdDuration___closed__5, &l_Std_Time_instOrdDuration___closed__5_once, _init_l_Std_Time_instOrdDuration___closed__5);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_neg(lean_object* v_duration_275_){
_start:
{
lean_object* v_second_276_; lean_object* v_nano_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_286_; 
v_second_276_ = lean_ctor_get(v_duration_275_, 0);
v_nano_277_ = lean_ctor_get(v_duration_275_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_duration_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_279_ = v_duration_275_;
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_nano_277_);
lean_inc(v_second_276_);
lean_dec(v_duration_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = lean_int_neg(v_second_276_);
lean_dec(v_second_276_);
v___x_282_ = lean_int_neg(v_nano_277_);
lean_dec(v_nano_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v___x_282_);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_284_ = v___x_279_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofSeconds(lean_object* v_s_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_s_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Duration_ofNanoseconds_spec__1(lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Rat_ofInt(v_a_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Time_Duration_ofNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1000000000u);
v___x_293_ = lean_nat_to_int(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object* v_s_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_295_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_296_ = lean_int_div(v_s_294_, v___x_295_);
v___x_297_ = lean_int_mod(v_s_294_, v___x_295_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds___boxed(lean_object* v_s_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Time_Duration_ofNanoseconds(v_s_299_);
lean_dec(v_s_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Duration_ofNanoseconds_spec__0(lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_nat_to_int(v_a_301_);
v___x_303_ = l_Rat_ofInt(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Std_Time_Duration_ofMillisecond___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1000000u);
v___x_305_ = lean_nat_to_int(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond(lean_object* v_s_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_308_ = lean_int_mul(v_s_306_, v___x_307_);
v___x_309_ = l_Std_Time_Duration_ofNanoseconds(v___x_308_);
lean_dec(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond___boxed(lean_object* v_s_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Time_Duration_ofMillisecond(v_s_310_);
lean_dec(v_s_310_);
return v_res_311_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Duration_isZero(lean_object* v_d_312_){
_start:
{
lean_object* v_second_313_; lean_object* v_nano_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_second_313_ = lean_ctor_get(v_d_312_, 0);
v_nano_314_ = lean_ctor_get(v_d_312_, 1);
v___x_315_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_316_ = lean_int_dec_eq(v_second_313_, v___x_315_);
if (v___x_316_ == 0)
{
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = lean_int_dec_eq(v_nano_314_, v___x_315_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_isZero___boxed(lean_object* v_d_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Std_Time_Duration_isZero(v_d_318_);
lean_dec_ref(v_d_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds(lean_object* v_duration_321_){
_start:
{
lean_object* v_second_322_; 
v_second_322_ = lean_ctor_get(v_duration_321_, 0);
lean_inc(v_second_322_);
return v_second_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds___boxed(lean_object* v_duration_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Time_Duration_toSeconds(v_duration_323_);
lean_dec_ref(v_duration_323_);
return v_res_324_;
}
}
static lean_object* _init_l_Std_Time_Duration_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1000u);
v___x_326_ = lean_nat_to_int(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds(lean_object* v_duration_327_){
_start:
{
lean_object* v_second_328_; lean_object* v_nano_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_millis_334_; 
v_second_328_ = lean_ctor_get(v_duration_327_, 0);
v_nano_329_ = lean_ctor_get(v_duration_327_, 1);
v___x_330_ = lean_obj_once(&l_Std_Time_Duration_toMilliseconds___closed__0, &l_Std_Time_Duration_toMilliseconds___closed__0_once, _init_l_Std_Time_Duration_toMilliseconds___closed__0);
v___x_331_ = lean_int_mul(v_second_328_, v___x_330_);
v___x_332_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_333_ = lean_int_ediv(v_nano_329_, v___x_332_);
v_millis_334_ = lean_int_add(v___x_331_, v___x_333_);
lean_dec(v___x_333_);
lean_dec(v___x_331_);
return v_millis_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds___boxed(lean_object* v_duration_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Time_Duration_toMilliseconds(v_duration_335_);
lean_dec_ref(v_duration_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds(lean_object* v_duration_337_){
_start:
{
lean_object* v_second_338_; lean_object* v_nano_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_nanos_342_; 
v_second_338_ = lean_ctor_get(v_duration_337_, 0);
v_nano_339_ = lean_ctor_get(v_duration_337_, 1);
v___x_340_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_341_ = lean_int_mul(v_second_338_, v___x_340_);
v_nanos_342_ = lean_int_add(v___x_341_, v_nano_339_);
lean_dec(v___x_341_);
return v_nanos_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds___boxed(lean_object* v_duration_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_Time_Duration_toNanoseconds(v_duration_343_);
lean_dec_ref(v_duration_343_);
return v_res_344_;
}
}
static lean_object* _init_l_Std_Time_Duration_instLE(void){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Duration_instDecidableLe(lean_object* v_x_346_, lean_object* v_y_347_){
_start:
{
lean_object* v_second_348_; lean_object* v_nano_349_; lean_object* v_second_350_; lean_object* v_nano_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_nanos_354_; lean_object* v___x_355_; lean_object* v_nanos_356_; uint8_t v___x_357_; 
v_second_348_ = lean_ctor_get(v_x_346_, 0);
v_nano_349_ = lean_ctor_get(v_x_346_, 1);
v_second_350_ = lean_ctor_get(v_y_347_, 0);
v_nano_351_ = lean_ctor_get(v_y_347_, 1);
v___x_352_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_353_ = lean_int_mul(v_second_348_, v___x_352_);
v_nanos_354_ = lean_int_add(v___x_353_, v_nano_349_);
lean_dec(v___x_353_);
v___x_355_ = lean_int_mul(v_second_350_, v___x_352_);
v_nanos_356_ = lean_int_add(v___x_355_, v_nano_351_);
lean_dec(v___x_355_);
v___x_357_ = lean_int_dec_le(v_nanos_354_, v_nanos_356_);
lean_dec(v_nanos_356_);
lean_dec(v_nanos_354_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLe___boxed(lean_object* v_x_358_, lean_object* v_y_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Std_Time_Duration_instDecidableLe(v_x_358_, v_y_359_);
lean_dec_ref(v_y_359_);
lean_dec_ref(v_x_358_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
static lean_object* _init_l_Std_Time_Duration_instLT(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
return v___x_362_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Duration_instDecidableLt(lean_object* v_x_363_, lean_object* v_y_364_){
_start:
{
lean_object* v_second_365_; lean_object* v_nano_366_; lean_object* v_second_367_; lean_object* v_nano_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_nanos_371_; lean_object* v___x_372_; lean_object* v_nanos_373_; uint8_t v___x_374_; 
v_second_365_ = lean_ctor_get(v_x_363_, 0);
v_nano_366_ = lean_ctor_get(v_x_363_, 1);
v_second_367_ = lean_ctor_get(v_y_364_, 0);
v_nano_368_ = lean_ctor_get(v_y_364_, 1);
v___x_369_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_370_ = lean_int_mul(v_second_365_, v___x_369_);
v_nanos_371_ = lean_int_add(v___x_370_, v_nano_366_);
lean_dec(v___x_370_);
v___x_372_ = lean_int_mul(v_second_367_, v___x_369_);
v_nanos_373_ = lean_int_add(v___x_372_, v_nano_368_);
lean_dec(v___x_372_);
v___x_374_ = lean_int_dec_lt(v_nanos_371_, v_nanos_373_);
lean_dec(v_nanos_373_);
lean_dec(v_nanos_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLt___boxed(lean_object* v_x_375_, lean_object* v_y_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Std_Time_Duration_instDecidableLt(v_x_375_, v_y_376_);
lean_dec_ref(v_y_376_);
lean_dec_ref(v_x_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
static lean_object* _init_l_Std_Time_Duration_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(60u);
v___x_380_ = lean_nat_to_int(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes(lean_object* v_tm_381_){
_start:
{
lean_object* v_second_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_second_382_ = lean_ctor_get(v_tm_381_, 0);
v___x_383_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v___x_384_ = lean_int_div(v_second_382_, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes___boxed(lean_object* v_tm_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_Time_Duration_toMinutes(v_tm_385_);
lean_dec_ref(v_tm_385_);
return v_res_386_;
}
}
static lean_object* _init_l_Std_Time_Duration_toDays___closed__0(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_unsigned_to_nat(86400u);
v___x_388_ = lean_nat_to_int(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays(lean_object* v_tm_389_){
_start:
{
lean_object* v_second_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_second_390_ = lean_ctor_get(v_tm_389_, 0);
v___x_391_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v___x_392_ = lean_int_div(v_second_390_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays___boxed(lean_object* v_tm_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Time_Duration_toDays(v_tm_393_);
lean_dec_ref(v_tm_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents(lean_object* v_secs_395_, lean_object* v_nanos_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_397_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_398_ = lean_int_mul(v_secs_395_, v___x_397_);
v___x_399_ = l_Std_Time_Nanosecond_Span_toOffset(v_nanos_396_);
v___x_400_ = lean_int_add(v___x_398_, v___x_399_);
lean_dec(v___x_399_);
lean_dec(v___x_398_);
v___x_401_ = l_Std_Time_Duration_ofNanoseconds(v___x_400_);
lean_dec(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents___boxed(lean_object* v_secs_402_, lean_object* v_nanos_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_Time_Duration_fromComponents(v_secs_402_, v_nanos_403_);
lean_dec(v_nanos_403_);
lean_dec(v_secs_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_add(lean_object* v_t_u2081_405_, lean_object* v_t_u2082_406_){
_start:
{
lean_object* v_second_407_; lean_object* v_nano_408_; lean_object* v_second_409_; lean_object* v_nano_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_second_407_ = lean_ctor_get(v_t_u2081_405_, 0);
v_nano_408_ = lean_ctor_get(v_t_u2081_405_, 1);
v_second_409_ = lean_ctor_get(v_t_u2082_406_, 0);
v_nano_410_ = lean_ctor_get(v_t_u2082_406_, 1);
v___x_411_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_412_ = lean_int_mul(v_second_407_, v___x_411_);
v___x_413_ = lean_int_add(v___x_412_, v_nano_408_);
lean_dec(v___x_412_);
v___x_414_ = lean_int_mul(v_second_409_, v___x_411_);
v___x_415_ = lean_int_add(v___x_414_, v_nano_410_);
lean_dec(v___x_414_);
v___x_416_ = lean_int_add(v___x_413_, v___x_415_);
lean_dec(v___x_415_);
lean_dec(v___x_413_);
v___x_417_ = l_Std_Time_Duration_ofNanoseconds(v___x_416_);
lean_dec(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_add___boxed(lean_object* v_t_u2081_418_, lean_object* v_t_u2082_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_Time_Duration_add(v_t_u2081_418_, v_t_u2082_419_);
lean_dec_ref(v_t_u2082_419_);
lean_dec_ref(v_t_u2081_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub(lean_object* v_t_u2081_421_, lean_object* v_t_u2082_422_){
_start:
{
lean_object* v_second_423_; lean_object* v_nano_424_; lean_object* v_second_425_; lean_object* v_nano_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_second_423_ = lean_ctor_get(v_t_u2082_422_, 0);
v_nano_424_ = lean_ctor_get(v_t_u2082_422_, 1);
v_second_425_ = lean_ctor_get(v_t_u2081_421_, 0);
v_nano_426_ = lean_ctor_get(v_t_u2081_421_, 1);
v___x_427_ = lean_int_neg(v_second_423_);
v___x_428_ = lean_int_neg(v_nano_424_);
v___x_429_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_430_ = lean_int_mul(v_second_425_, v___x_429_);
v___x_431_ = lean_int_add(v___x_430_, v_nano_426_);
lean_dec(v___x_430_);
v___x_432_ = lean_int_mul(v___x_427_, v___x_429_);
lean_dec(v___x_427_);
v___x_433_ = lean_int_add(v___x_432_, v___x_428_);
lean_dec(v___x_428_);
lean_dec(v___x_432_);
v___x_434_ = lean_int_add(v___x_431_, v___x_433_);
lean_dec(v___x_433_);
lean_dec(v___x_431_);
v___x_435_ = l_Std_Time_Duration_ofNanoseconds(v___x_434_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub___boxed(lean_object* v_t_u2081_436_, lean_object* v_t_u2082_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_Time_Duration_sub(v_t_u2081_436_, v_t_u2082_437_);
lean_dec_ref(v_t_u2082_437_);
lean_dec_ref(v_t_u2081_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds(lean_object* v_t_439_, lean_object* v_s_440_){
_start:
{
lean_object* v_second_441_; lean_object* v_nano_442_; lean_object* v___x_443_; lean_object* v_second_444_; lean_object* v_nano_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_second_441_ = lean_ctor_get(v_t_439_, 0);
v_nano_442_ = lean_ctor_get(v_t_439_, 1);
v___x_443_ = l_Std_Time_Duration_ofNanoseconds(v_s_440_);
v_second_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_second_444_);
v_nano_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_nano_445_);
lean_dec_ref(v___x_443_);
v___x_446_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_447_ = lean_int_mul(v_second_441_, v___x_446_);
v___x_448_ = lean_int_add(v___x_447_, v_nano_442_);
lean_dec(v___x_447_);
v___x_449_ = lean_int_mul(v_second_444_, v___x_446_);
lean_dec(v_second_444_);
v___x_450_ = lean_int_add(v___x_449_, v_nano_445_);
lean_dec(v_nano_445_);
lean_dec(v___x_449_);
v___x_451_ = lean_int_add(v___x_448_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v___x_448_);
v___x_452_ = l_Std_Time_Duration_ofNanoseconds(v___x_451_);
lean_dec(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds___boxed(lean_object* v_t_453_, lean_object* v_s_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_Time_Duration_addNanoseconds(v_t_453_, v_s_454_);
lean_dec(v_s_454_);
lean_dec_ref(v_t_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds(lean_object* v_t_456_, lean_object* v_s_457_){
_start:
{
lean_object* v_second_458_; lean_object* v_nano_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_second_463_; lean_object* v_nano_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_second_458_ = lean_ctor_get(v_t_456_, 0);
v_nano_459_ = lean_ctor_get(v_t_456_, 1);
v___x_460_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_461_ = lean_int_mul(v_s_457_, v___x_460_);
v___x_462_ = l_Std_Time_Duration_ofNanoseconds(v___x_461_);
lean_dec(v___x_461_);
v_second_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_second_463_);
v_nano_464_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_nano_464_);
lean_dec_ref(v___x_462_);
v___x_465_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_466_ = lean_int_mul(v_second_458_, v___x_465_);
v___x_467_ = lean_int_add(v___x_466_, v_nano_459_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_mul(v_second_463_, v___x_465_);
lean_dec(v_second_463_);
v___x_469_ = lean_int_add(v___x_468_, v_nano_464_);
lean_dec(v_nano_464_);
lean_dec(v___x_468_);
v___x_470_ = lean_int_add(v___x_467_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_467_);
v___x_471_ = l_Std_Time_Duration_ofNanoseconds(v___x_470_);
lean_dec(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds___boxed(lean_object* v_t_472_, lean_object* v_s_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Time_Duration_addMilliseconds(v_t_472_, v_s_473_);
lean_dec(v_s_473_);
lean_dec_ref(v_t_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds(lean_object* v_t_475_, lean_object* v_s_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_second_480_; lean_object* v_nano_481_; lean_object* v_second_482_; lean_object* v_nano_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_477_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_478_ = lean_int_mul(v_s_476_, v___x_477_);
v___x_479_ = l_Std_Time_Duration_ofNanoseconds(v___x_478_);
lean_dec(v___x_478_);
v_second_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_second_480_);
v_nano_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_nano_481_);
lean_dec_ref(v___x_479_);
v_second_482_ = lean_ctor_get(v_t_475_, 0);
v_nano_483_ = lean_ctor_get(v_t_475_, 1);
v___x_484_ = lean_int_neg(v_second_480_);
lean_dec(v_second_480_);
v___x_485_ = lean_int_neg(v_nano_481_);
lean_dec(v_nano_481_);
v___x_486_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_487_ = lean_int_mul(v_second_482_, v___x_486_);
v___x_488_ = lean_int_add(v___x_487_, v_nano_483_);
lean_dec(v___x_487_);
v___x_489_ = lean_int_mul(v___x_484_, v___x_486_);
lean_dec(v___x_484_);
v___x_490_ = lean_int_add(v___x_489_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v___x_489_);
v___x_491_ = lean_int_add(v___x_488_, v___x_490_);
lean_dec(v___x_490_);
lean_dec(v___x_488_);
v___x_492_ = l_Std_Time_Duration_ofNanoseconds(v___x_491_);
lean_dec(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds___boxed(lean_object* v_t_493_, lean_object* v_s_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Time_Duration_subMilliseconds(v_t_493_, v_s_494_);
lean_dec(v_s_494_);
lean_dec_ref(v_t_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds(lean_object* v_t_496_, lean_object* v_s_497_){
_start:
{
lean_object* v___x_498_; lean_object* v_second_499_; lean_object* v_nano_500_; lean_object* v_second_501_; lean_object* v_nano_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_498_ = l_Std_Time_Duration_ofNanoseconds(v_s_497_);
v_second_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_second_499_);
v_nano_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_nano_500_);
lean_dec_ref(v___x_498_);
v_second_501_ = lean_ctor_get(v_t_496_, 0);
v_nano_502_ = lean_ctor_get(v_t_496_, 1);
v___x_503_ = lean_int_neg(v_second_499_);
lean_dec(v_second_499_);
v___x_504_ = lean_int_neg(v_nano_500_);
lean_dec(v_nano_500_);
v___x_505_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_506_ = lean_int_mul(v_second_501_, v___x_505_);
v___x_507_ = lean_int_add(v___x_506_, v_nano_502_);
lean_dec(v___x_506_);
v___x_508_ = lean_int_mul(v___x_503_, v___x_505_);
lean_dec(v___x_503_);
v___x_509_ = lean_int_add(v___x_508_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_508_);
v___x_510_ = lean_int_add(v___x_507_, v___x_509_);
lean_dec(v___x_509_);
lean_dec(v___x_507_);
v___x_511_ = l_Std_Time_Duration_ofNanoseconds(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds___boxed(lean_object* v_t_512_, lean_object* v_s_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Time_Duration_subNanoseconds(v_t_512_, v_s_513_);
lean_dec(v_s_513_);
lean_dec_ref(v_t_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds(lean_object* v_t_515_, lean_object* v_s_516_){
_start:
{
lean_object* v_second_517_; lean_object* v_nano_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_second_517_ = lean_ctor_get(v_t_515_, 0);
v_nano_518_ = lean_ctor_get(v_t_515_, 1);
v___x_519_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_520_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_521_ = lean_int_mul(v_second_517_, v___x_520_);
v___x_522_ = lean_int_add(v___x_521_, v_nano_518_);
lean_dec(v___x_521_);
v___x_523_ = lean_int_mul(v_s_516_, v___x_520_);
v___x_524_ = lean_int_add(v___x_523_, v___x_519_);
lean_dec(v___x_523_);
v___x_525_ = lean_int_add(v___x_522_, v___x_524_);
lean_dec(v___x_524_);
lean_dec(v___x_522_);
v___x_526_ = l_Std_Time_Duration_ofNanoseconds(v___x_525_);
lean_dec(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds___boxed(lean_object* v_t_527_, lean_object* v_s_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Time_Duration_addSeconds(v_t_527_, v_s_528_);
lean_dec(v_s_528_);
lean_dec_ref(v_t_527_);
return v_res_529_;
}
}
static lean_object* _init_l_Std_Time_Duration_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_531_ = lean_int_neg(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds(lean_object* v_t_532_, lean_object* v_s_533_){
_start:
{
lean_object* v_second_534_; lean_object* v_nano_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_second_534_ = lean_ctor_get(v_t_532_, 0);
v_nano_535_ = lean_ctor_get(v_t_532_, 1);
v___x_536_ = lean_int_neg(v_s_533_);
v___x_537_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_538_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_539_ = lean_int_mul(v_second_534_, v___x_538_);
v___x_540_ = lean_int_add(v___x_539_, v_nano_535_);
lean_dec(v___x_539_);
v___x_541_ = lean_int_mul(v___x_536_, v___x_538_);
lean_dec(v___x_536_);
v___x_542_ = lean_int_add(v___x_541_, v___x_537_);
lean_dec(v___x_541_);
v___x_543_ = lean_int_add(v___x_540_, v___x_542_);
lean_dec(v___x_542_);
lean_dec(v___x_540_);
v___x_544_ = l_Std_Time_Duration_ofNanoseconds(v___x_543_);
lean_dec(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds___boxed(lean_object* v_t_545_, lean_object* v_s_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_Duration_subSeconds(v_t_545_, v_s_546_);
lean_dec(v_s_546_);
lean_dec_ref(v_t_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes(lean_object* v_t_548_, lean_object* v_m_549_){
_start:
{
lean_object* v_second_550_; lean_object* v_nano_551_; lean_object* v___x_552_; lean_object* v_seconds_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_second_550_ = lean_ctor_get(v_t_548_, 0);
v_nano_551_ = lean_ctor_get(v_t_548_, 1);
v___x_552_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v_seconds_553_ = lean_int_mul(v_m_549_, v___x_552_);
v___x_554_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_555_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_556_ = lean_int_mul(v_second_550_, v___x_555_);
v___x_557_ = lean_int_add(v___x_556_, v_nano_551_);
lean_dec(v___x_556_);
v___x_558_ = lean_int_mul(v_seconds_553_, v___x_555_);
lean_dec(v_seconds_553_);
v___x_559_ = lean_int_add(v___x_558_, v___x_554_);
lean_dec(v___x_558_);
v___x_560_ = lean_int_add(v___x_557_, v___x_559_);
lean_dec(v___x_559_);
lean_dec(v___x_557_);
v___x_561_ = l_Std_Time_Duration_ofNanoseconds(v___x_560_);
lean_dec(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes___boxed(lean_object* v_t_562_, lean_object* v_m_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Time_Duration_addMinutes(v_t_562_, v_m_563_);
lean_dec(v_m_563_);
lean_dec_ref(v_t_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes(lean_object* v_t_565_, lean_object* v_m_566_){
_start:
{
lean_object* v_second_567_; lean_object* v_nano_568_; lean_object* v___x_569_; lean_object* v_seconds_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_second_567_ = lean_ctor_get(v_t_565_, 0);
v_nano_568_ = lean_ctor_get(v_t_565_, 1);
v___x_569_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v_seconds_570_ = lean_int_mul(v_m_566_, v___x_569_);
v___x_571_ = lean_int_neg(v_seconds_570_);
lean_dec(v_seconds_570_);
v___x_572_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_573_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_574_ = lean_int_mul(v_second_567_, v___x_573_);
v___x_575_ = lean_int_add(v___x_574_, v_nano_568_);
lean_dec(v___x_574_);
v___x_576_ = lean_int_mul(v___x_571_, v___x_573_);
lean_dec(v___x_571_);
v___x_577_ = lean_int_add(v___x_576_, v___x_572_);
lean_dec(v___x_576_);
v___x_578_ = lean_int_add(v___x_575_, v___x_577_);
lean_dec(v___x_577_);
lean_dec(v___x_575_);
v___x_579_ = l_Std_Time_Duration_ofNanoseconds(v___x_578_);
lean_dec(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes___boxed(lean_object* v_t_580_, lean_object* v_m_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Time_Duration_subMinutes(v_t_580_, v_m_581_);
lean_dec(v_m_581_);
lean_dec_ref(v_t_580_);
return v_res_582_;
}
}
static lean_object* _init_l_Std_Time_Duration_addHours___closed__0(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(3600u);
v___x_584_ = lean_nat_to_int(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours(lean_object* v_t_585_, lean_object* v_h_586_){
_start:
{
lean_object* v_second_587_; lean_object* v_nano_588_; lean_object* v___x_589_; lean_object* v_seconds_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_second_587_ = lean_ctor_get(v_t_585_, 0);
v_nano_588_ = lean_ctor_get(v_t_585_, 1);
v___x_589_ = lean_obj_once(&l_Std_Time_Duration_addHours___closed__0, &l_Std_Time_Duration_addHours___closed__0_once, _init_l_Std_Time_Duration_addHours___closed__0);
v_seconds_590_ = lean_int_mul(v_h_586_, v___x_589_);
v___x_591_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_592_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_593_ = lean_int_mul(v_second_587_, v___x_592_);
v___x_594_ = lean_int_add(v___x_593_, v_nano_588_);
lean_dec(v___x_593_);
v___x_595_ = lean_int_mul(v_seconds_590_, v___x_592_);
lean_dec(v_seconds_590_);
v___x_596_ = lean_int_add(v___x_595_, v___x_591_);
lean_dec(v___x_595_);
v___x_597_ = lean_int_add(v___x_594_, v___x_596_);
lean_dec(v___x_596_);
lean_dec(v___x_594_);
v___x_598_ = l_Std_Time_Duration_ofNanoseconds(v___x_597_);
lean_dec(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours___boxed(lean_object* v_t_599_, lean_object* v_h_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Time_Duration_addHours(v_t_599_, v_h_600_);
lean_dec(v_h_600_);
lean_dec_ref(v_t_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours(lean_object* v_t_602_, lean_object* v_h_603_){
_start:
{
lean_object* v_second_604_; lean_object* v_nano_605_; lean_object* v___x_606_; lean_object* v_seconds_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_second_604_ = lean_ctor_get(v_t_602_, 0);
v_nano_605_ = lean_ctor_get(v_t_602_, 1);
v___x_606_ = lean_obj_once(&l_Std_Time_Duration_addHours___closed__0, &l_Std_Time_Duration_addHours___closed__0_once, _init_l_Std_Time_Duration_addHours___closed__0);
v_seconds_607_ = lean_int_mul(v_h_603_, v___x_606_);
v___x_608_ = lean_int_neg(v_seconds_607_);
lean_dec(v_seconds_607_);
v___x_609_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_610_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_611_ = lean_int_mul(v_second_604_, v___x_610_);
v___x_612_ = lean_int_add(v___x_611_, v_nano_605_);
lean_dec(v___x_611_);
v___x_613_ = lean_int_mul(v___x_608_, v___x_610_);
lean_dec(v___x_608_);
v___x_614_ = lean_int_add(v___x_613_, v___x_609_);
lean_dec(v___x_613_);
v___x_615_ = lean_int_add(v___x_612_, v___x_614_);
lean_dec(v___x_614_);
lean_dec(v___x_612_);
v___x_616_ = l_Std_Time_Duration_ofNanoseconds(v___x_615_);
lean_dec(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours___boxed(lean_object* v_t_617_, lean_object* v_h_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Time_Duration_subHours(v_t_617_, v_h_618_);
lean_dec(v_h_618_);
lean_dec_ref(v_t_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays(lean_object* v_t_620_, lean_object* v_d_621_){
_start:
{
lean_object* v_second_622_; lean_object* v_nano_623_; lean_object* v___x_624_; lean_object* v_seconds_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_second_622_ = lean_ctor_get(v_t_620_, 0);
v_nano_623_ = lean_ctor_get(v_t_620_, 1);
v___x_624_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v_seconds_625_ = lean_int_mul(v_d_621_, v___x_624_);
v___x_626_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_627_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_628_ = lean_int_mul(v_second_622_, v___x_627_);
v___x_629_ = lean_int_add(v___x_628_, v_nano_623_);
lean_dec(v___x_628_);
v___x_630_ = lean_int_mul(v_seconds_625_, v___x_627_);
lean_dec(v_seconds_625_);
v___x_631_ = lean_int_add(v___x_630_, v___x_626_);
lean_dec(v___x_630_);
v___x_632_ = lean_int_add(v___x_629_, v___x_631_);
lean_dec(v___x_631_);
lean_dec(v___x_629_);
v___x_633_ = l_Std_Time_Duration_ofNanoseconds(v___x_632_);
lean_dec(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays___boxed(lean_object* v_t_634_, lean_object* v_d_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Time_Duration_addDays(v_t_634_, v_d_635_);
lean_dec(v_d_635_);
lean_dec_ref(v_t_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays(lean_object* v_t_637_, lean_object* v_d_638_){
_start:
{
lean_object* v_second_639_; lean_object* v_nano_640_; lean_object* v___x_641_; lean_object* v_seconds_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_second_639_ = lean_ctor_get(v_t_637_, 0);
v_nano_640_ = lean_ctor_get(v_t_637_, 1);
v___x_641_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v_seconds_642_ = lean_int_mul(v_d_638_, v___x_641_);
v___x_643_ = lean_int_neg(v_seconds_642_);
lean_dec(v_seconds_642_);
v___x_644_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_645_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_646_ = lean_int_mul(v_second_639_, v___x_645_);
v___x_647_ = lean_int_add(v___x_646_, v_nano_640_);
lean_dec(v___x_646_);
v___x_648_ = lean_int_mul(v___x_643_, v___x_645_);
lean_dec(v___x_643_);
v___x_649_ = lean_int_add(v___x_648_, v___x_644_);
lean_dec(v___x_648_);
v___x_650_ = lean_int_add(v___x_647_, v___x_649_);
lean_dec(v___x_649_);
lean_dec(v___x_647_);
v___x_651_ = l_Std_Time_Duration_ofNanoseconds(v___x_650_);
lean_dec(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays___boxed(lean_object* v_t_652_, lean_object* v_d_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Time_Duration_subDays(v_t_652_, v_d_653_);
lean_dec(v_d_653_);
lean_dec_ref(v_t_652_);
return v_res_654_;
}
}
static lean_object* _init_l_Std_Time_Duration_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(604800u);
v___x_656_ = lean_nat_to_int(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks(lean_object* v_t_657_, lean_object* v_w_658_){
_start:
{
lean_object* v_second_659_; lean_object* v_nano_660_; lean_object* v___x_661_; lean_object* v_seconds_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_second_659_ = lean_ctor_get(v_t_657_, 0);
v_nano_660_ = lean_ctor_get(v_t_657_, 1);
v___x_661_ = lean_obj_once(&l_Std_Time_Duration_addWeeks___closed__0, &l_Std_Time_Duration_addWeeks___closed__0_once, _init_l_Std_Time_Duration_addWeeks___closed__0);
v_seconds_662_ = lean_int_mul(v_w_658_, v___x_661_);
v___x_663_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_664_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_665_ = lean_int_mul(v_second_659_, v___x_664_);
v___x_666_ = lean_int_add(v___x_665_, v_nano_660_);
lean_dec(v___x_665_);
v___x_667_ = lean_int_mul(v_seconds_662_, v___x_664_);
lean_dec(v_seconds_662_);
v___x_668_ = lean_int_add(v___x_667_, v___x_663_);
lean_dec(v___x_667_);
v___x_669_ = lean_int_add(v___x_666_, v___x_668_);
lean_dec(v___x_668_);
lean_dec(v___x_666_);
v___x_670_ = l_Std_Time_Duration_ofNanoseconds(v___x_669_);
lean_dec(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks___boxed(lean_object* v_t_671_, lean_object* v_w_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Time_Duration_addWeeks(v_t_671_, v_w_672_);
lean_dec(v_w_672_);
lean_dec_ref(v_t_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks(lean_object* v_t_674_, lean_object* v_w_675_){
_start:
{
lean_object* v_second_676_; lean_object* v_nano_677_; lean_object* v___x_678_; lean_object* v_seconds_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_second_676_ = lean_ctor_get(v_t_674_, 0);
v_nano_677_ = lean_ctor_get(v_t_674_, 1);
v___x_678_ = lean_obj_once(&l_Std_Time_Duration_addWeeks___closed__0, &l_Std_Time_Duration_addWeeks___closed__0_once, _init_l_Std_Time_Duration_addWeeks___closed__0);
v_seconds_679_ = lean_int_mul(v_w_675_, v___x_678_);
v___x_680_ = lean_int_neg(v_seconds_679_);
lean_dec(v_seconds_679_);
v___x_681_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_682_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_683_ = lean_int_mul(v_second_676_, v___x_682_);
v___x_684_ = lean_int_add(v___x_683_, v_nano_677_);
lean_dec(v___x_683_);
v___x_685_ = lean_int_mul(v___x_680_, v___x_682_);
lean_dec(v___x_680_);
v___x_686_ = lean_int_add(v___x_685_, v___x_681_);
lean_dec(v___x_685_);
v___x_687_ = lean_int_add(v___x_684_, v___x_686_);
lean_dec(v___x_686_);
lean_dec(v___x_684_);
v___x_688_ = l_Std_Time_Duration_ofNanoseconds(v___x_687_);
lean_dec(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks___boxed(lean_object* v_t_689_, lean_object* v_w_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Time_Duration_subWeeks(v_t_689_, v_w_690_);
lean_dec(v_w_690_);
lean_dec_ref(v_t_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0(lean_object* v_i_751_, lean_object* v_d_752_){
_start:
{
lean_object* v_second_753_; lean_object* v_nano_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_second_753_ = lean_ctor_get(v_d_752_, 0);
v_nano_754_ = lean_ctor_get(v_d_752_, 1);
v___x_755_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_756_ = lean_int_mul(v_second_753_, v___x_755_);
v___x_757_ = lean_int_add(v___x_756_, v_nano_754_);
lean_dec(v___x_756_);
v___x_758_ = lean_int_mul(v___x_757_, v_i_751_);
lean_dec(v___x_757_);
v___x_759_ = l_Std_Time_Duration_ofNanoseconds(v___x_758_);
lean_dec(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0___boxed(lean_object* v_i_760_, lean_object* v_d_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_Time_Duration_instHMulInt___lam__0(v_i_760_, v_d_761_);
lean_dec_ref(v_d_761_);
lean_dec(v_i_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0(lean_object* v_d_765_, lean_object* v_i_766_){
_start:
{
lean_object* v_second_767_; lean_object* v_nano_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_second_767_ = lean_ctor_get(v_d_765_, 0);
v_nano_768_ = lean_ctor_get(v_d_765_, 1);
v___x_769_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_770_ = lean_int_mul(v_second_767_, v___x_769_);
v___x_771_ = lean_int_add(v___x_770_, v_nano_768_);
lean_dec(v___x_770_);
v___x_772_ = lean_int_mul(v___x_771_, v_i_766_);
lean_dec(v___x_771_);
v___x_773_ = l_Std_Time_Duration_ofNanoseconds(v___x_772_);
lean_dec(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0___boxed(lean_object* v_d_774_, lean_object* v_i_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_Time_Duration_instHMulInt__1___lam__0(v_d_774_, v_i_775_);
lean_dec(v_i_775_);
lean_dec_ref(v_d_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0(lean_object* v_pt_779_, lean_object* v_d_780_){
_start:
{
lean_object* v_second_781_; lean_object* v_nano_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_second_781_ = lean_ctor_get(v_d_780_, 0);
v_nano_782_ = lean_ctor_get(v_d_780_, 1);
v___x_783_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_784_ = lean_int_mul(v_second_781_, v___x_783_);
v___x_785_ = lean_int_add(v___x_784_, v_nano_782_);
lean_dec(v___x_784_);
v___x_786_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_779_);
v___x_787_ = lean_int_add(v___x_785_, v___x_786_);
lean_dec(v___x_786_);
lean_dec(v___x_785_);
v___x_788_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_787_);
lean_dec(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed(lean_object* v_pt_789_, lean_object* v_d_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_Time_Duration_instHAddPlainTime___lam__0(v_pt_789_, v_d_790_);
lean_dec_ref(v_d_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0(lean_object* v_pt_794_, lean_object* v_d_795_){
_start:
{
lean_object* v_second_796_; lean_object* v_nano_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_second_796_ = lean_ctor_get(v_d_795_, 0);
v_nano_797_ = lean_ctor_get(v_d_795_, 1);
v___x_798_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_794_);
v___x_799_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_800_ = lean_int_mul(v_second_796_, v___x_799_);
v___x_801_ = lean_int_add(v___x_800_, v_nano_797_);
lean_dec(v___x_800_);
v___x_802_ = lean_int_sub(v___x_798_, v___x_801_);
lean_dec(v___x_801_);
lean_dec(v___x_798_);
v___x_803_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_802_);
lean_dec(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed(lean_object* v_pt_804_, lean_object* v_d_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Time_Duration_instHSubPlainTime___lam__0(v_pt_804_, v_d_805_);
lean_dec_ref(v_d_805_);
return v_res_806_;
}
}
lean_object* runtime_initialize_Std_Time_Date(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedDuration = _init_l_Std_Time_instInhabitedDuration();
lean_mark_persistent(l_Std_Time_instInhabitedDuration);
l_Std_Time_instOrdDuration = _init_l_Std_Time_instOrdDuration();
lean_mark_persistent(l_Std_Time_instOrdDuration);
l_Std_Time_Duration_instLE = _init_l_Std_Time_Duration_instLE();
lean_mark_persistent(l_Std_Time_Duration_instLE);
l_Std_Time_Duration_instLT = _init_l_Std_Time_Duration_instLT();
lean_mark_persistent(l_Std_Time_Duration_instLT);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Duration(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Duration(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Duration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Duration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Duration(builtin);
}
#ifdef __cplusplus
}
#endif
