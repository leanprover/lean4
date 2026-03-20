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
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
lean_object* v___y_139_; lean_object* v___y_140_; lean_object* v_second_144_; lean_object* v_nano_145_; lean_object* v_fst_147_; lean_object* v_fst_148_; lean_object* v_snd_149_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_second_144_ = lean_ctor_get(v_s_137_, 0);
lean_inc(v_second_144_);
v_nano_145_ = lean_ctor_get(v_s_137_, 1);
lean_inc(v_nano_145_);
lean_dec_ref(v_s_137_);
v___x_160_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_161_ = lean_int_dec_lt(v___x_160_, v_second_144_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = lean_int_dec_lt(v_second_144_, v___x_160_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; 
v___x_163_ = lean_int_dec_lt(v_nano_145_, v___x_160_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_145_);
v_fst_147_ = v___x_164_;
v_fst_148_ = v_second_144_;
v_snd_149_ = v_nano_145_;
goto v___jp_146_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_166_ = lean_int_neg(v_second_144_);
lean_dec(v_second_144_);
v___x_167_ = lean_int_neg(v_nano_145_);
v_fst_147_ = v___x_165_;
v_fst_148_ = v___x_166_;
v_snd_149_ = v___x_167_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_169_ = lean_int_neg(v_second_144_);
lean_dec(v_second_144_);
v___x_170_ = lean_int_neg(v_nano_145_);
v_fst_147_ = v___x_168_;
v_fst_148_ = v___x_169_;
v_snd_149_ = v___x_170_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_145_);
v_fst_147_ = v___x_171_;
v_fst_148_ = v_second_144_;
v_snd_149_ = v_nano_145_;
goto v___jp_146_;
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
v___jp_146_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = l_Int_repr(v_fst_148_);
lean_dec(v_fst_148_);
v___x_151_ = lean_string_append(v_fst_147_, v___x_150_);
lean_dec_ref(v___x_150_);
v___x_152_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_153_ = lean_int_dec_eq(v_nano_145_, v___x_152_);
lean_dec(v_nano_145_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_154_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__2));
v___x_155_ = lean_unsigned_to_nat(9u);
v___x_156_ = l_Int_repr(v_snd_149_);
lean_dec(v_snd_149_);
v___x_157_ = l_Std_Time_instToStringDuration_leftPad(v___x_155_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = lean_string_append(v___x_154_, v___x_157_);
lean_dec_ref(v___x_157_);
v___y_139_ = v___x_151_;
v___y_140_ = v___x_158_;
goto v___jp_138_;
}
else
{
lean_object* v___x_159_; 
lean_dec(v_snd_149_);
v___x_159_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___y_139_ = v___x_151_;
v___y_140_ = v___x_159_;
goto v___jp_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0(lean_object* v_s_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v_second_184_; lean_object* v_nano_185_; lean_object* v_fst_187_; lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_second_184_ = lean_ctor_get(v_s_174_, 0);
lean_inc(v_second_184_);
v_nano_185_ = lean_ctor_get(v_s_174_, 1);
lean_inc(v_nano_185_);
lean_dec_ref(v_s_174_);
v___x_200_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_201_ = lean_int_dec_lt(v___x_200_, v_second_184_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = lean_int_dec_lt(v_second_184_, v___x_200_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
v___x_203_ = lean_int_dec_lt(v_nano_185_, v___x_200_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_185_);
v_fst_187_ = v___x_204_;
v_fst_188_ = v_second_184_;
v_snd_189_ = v_nano_185_;
goto v___jp_186_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_206_ = lean_int_neg(v_second_184_);
lean_dec(v_second_184_);
v___x_207_ = lean_int_neg(v_nano_185_);
v_fst_187_ = v___x_205_;
v_fst_188_ = v___x_206_;
v_snd_189_ = v___x_207_;
goto v___jp_186_;
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_209_ = lean_int_neg(v_second_184_);
lean_dec(v_second_184_);
v___x_210_ = lean_int_neg(v_nano_185_);
v_fst_187_ = v___x_208_;
v_fst_188_ = v___x_209_;
v_snd_189_ = v___x_210_;
goto v___jp_186_;
}
}
else
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_185_);
v_fst_187_ = v___x_211_;
v_fst_188_ = v_second_184_;
v_snd_189_ = v_nano_185_;
goto v___jp_186_;
}
v___jp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_179_ = lean_string_append(v___y_177_, v___y_178_);
lean_dec_ref(v___y_178_);
v___x_180_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__0));
v___x_181_ = lean_string_append(v___x_179_, v___x_180_);
v___x_182_ = l_String_quote(v___x_181_);
v___x_183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
v___jp_186_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_190_ = l_Int_repr(v_fst_188_);
lean_dec(v_fst_188_);
v___x_191_ = lean_string_append(v_fst_187_, v___x_190_);
lean_dec_ref(v___x_190_);
v___x_192_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_193_ = lean_int_dec_eq(v_nano_185_, v___x_192_);
lean_dec(v_nano_185_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__2));
v___x_195_ = lean_unsigned_to_nat(9u);
v___x_196_ = l_Int_repr(v_snd_189_);
lean_dec(v_snd_189_);
v___x_197_ = l_Std_Time_instToStringDuration_leftPad(v___x_195_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_string_append(v___x_194_, v___x_197_);
lean_dec_ref(v___x_197_);
v___y_177_ = v___x_191_;
v___y_178_ = v___x_198_;
goto v___jp_176_;
}
else
{
lean_object* v___x_199_; 
lean_dec(v_snd_189_);
v___x_199_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___y_177_ = v___x_191_;
v___y_178_ = v___x_199_;
goto v___jp_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0___boxed(lean_object* v_s_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_instReprDuration__1___lam__0(v_s_212_, v___y_213_);
lean_dec(v___y_213_);
return v_res_214_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration___closed__0(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_to_int(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_obj_once(&l_Std_Time_instInhabitedDuration___closed__0, &l_Std_Time_instInhabitedDuration___closed__0_once, _init_l_Std_Time_instInhabitedDuration___closed__0);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Std_Time_instInhabitedDuration___closed__1, &l_Std_Time_instInhabitedDuration___closed__1_once, _init_l_Std_Time_instInhabitedDuration___closed__1);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOfNatDuration(lean_object* v_n_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_nat_to_int(v_n_222_);
v___x_224_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0(lean_object* v_x_226_){
_start:
{
lean_object* v_second_227_; 
v_second_227_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_second_227_);
return v_second_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Time_instOrdDuration___lam__0(v_x_228_);
lean_dec_ref(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1(lean_object* v_x_230_){
_start:
{
lean_object* v_nano_231_; 
v_nano_231_ = lean_ctor_get(v_x_230_, 1);
lean_inc(v_nano_231_);
return v_nano_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1___boxed(lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Time_instOrdDuration___lam__1(v_x_232_);
lean_dec_ref(v_x_232_);
return v_res_233_;
}
}
static lean_object* _init_l_Std_Time_instOrdDuration___closed__4(void){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___f_240_ = ((lean_object*)(l_Std_Time_instOrdDuration___closed__1));
v___x_241_ = l_Std_Time_Nanosecond_instOrdSpan;
v___x_242_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, lean_box(0));
lean_closure_set(v___x_242_, 2, v___x_241_);
lean_closure_set(v___x_242_, 3, v___f_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Std_Time_instOrdDuration___closed__5(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Std_Time_instOrdDuration___closed__4, &l_Std_Time_instOrdDuration___closed__4_once, _init_l_Std_Time_instOrdDuration___closed__4);
v___x_244_ = ((lean_object*)(l_Std_Time_instOrdDuration___closed__3));
v___x_245_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, lean_box(0));
lean_closure_set(v___x_245_, 2, v___x_244_);
lean_closure_set(v___x_245_, 3, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Std_Time_instOrdDuration(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Std_Time_instOrdDuration___closed__5, &l_Std_Time_instOrdDuration___closed__5_once, _init_l_Std_Time_instOrdDuration___closed__5);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_neg(lean_object* v_duration_247_){
_start:
{
lean_object* v_second_248_; lean_object* v_nano_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_258_; 
v_second_248_ = lean_ctor_get(v_duration_247_, 0);
v_nano_249_ = lean_ctor_get(v_duration_247_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_duration_247_);
if (v_isSharedCheck_258_ == 0)
{
v___x_251_ = v_duration_247_;
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_nano_249_);
lean_inc(v_second_248_);
lean_dec(v_duration_247_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_253_ = lean_int_neg(v_second_248_);
lean_dec(v_second_248_);
v___x_254_ = lean_int_neg(v_nano_249_);
lean_dec(v_nano_249_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_254_);
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofSeconds(lean_object* v_s_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_s_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Duration_ofNanoseconds_spec__1(lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Rat_ofInt(v_a_262_);
return v___x_263_;
}
}
static lean_object* _init_l_Std_Time_Duration_ofNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1000000000u);
v___x_265_ = lean_nat_to_int(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object* v_s_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_268_ = lean_int_div(v_s_266_, v___x_267_);
v___x_269_ = lean_int_mod(v_s_266_, v___x_267_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds___boxed(lean_object* v_s_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_Duration_ofNanoseconds(v_s_271_);
lean_dec(v_s_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Duration_ofNanoseconds_spec__0(lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_nat_to_int(v_a_273_);
v___x_275_ = l_Rat_ofInt(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Std_Time_Duration_ofMillisecond___closed__0(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(1000000u);
v___x_277_ = lean_nat_to_int(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond(lean_object* v_s_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_280_ = lean_int_mul(v_s_278_, v___x_279_);
v___x_281_ = l_Std_Time_Duration_ofNanoseconds(v___x_280_);
lean_dec(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond___boxed(lean_object* v_s_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Time_Duration_ofMillisecond(v_s_282_);
lean_dec(v_s_282_);
return v_res_283_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Duration_isZero(lean_object* v_d_284_){
_start:
{
lean_object* v_second_285_; lean_object* v_nano_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_second_285_ = lean_ctor_get(v_d_284_, 0);
v_nano_286_ = lean_ctor_get(v_d_284_, 1);
v___x_287_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_288_ = lean_int_dec_eq(v_second_285_, v___x_287_);
if (v___x_288_ == 0)
{
return v___x_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = lean_int_dec_eq(v_nano_286_, v___x_287_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_isZero___boxed(lean_object* v_d_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_Time_Duration_isZero(v_d_290_);
lean_dec_ref(v_d_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds(lean_object* v_duration_293_){
_start:
{
lean_object* v_second_294_; 
v_second_294_ = lean_ctor_get(v_duration_293_, 0);
lean_inc(v_second_294_);
return v_second_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds___boxed(lean_object* v_duration_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Time_Duration_toSeconds(v_duration_295_);
lean_dec_ref(v_duration_295_);
return v_res_296_;
}
}
static lean_object* _init_l_Std_Time_Duration_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1000u);
v___x_298_ = lean_nat_to_int(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds(lean_object* v_duration_299_){
_start:
{
lean_object* v_second_300_; lean_object* v_nano_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_millis_306_; 
v_second_300_ = lean_ctor_get(v_duration_299_, 0);
v_nano_301_ = lean_ctor_get(v_duration_299_, 1);
v___x_302_ = lean_obj_once(&l_Std_Time_Duration_toMilliseconds___closed__0, &l_Std_Time_Duration_toMilliseconds___closed__0_once, _init_l_Std_Time_Duration_toMilliseconds___closed__0);
v___x_303_ = lean_int_mul(v_second_300_, v___x_302_);
v___x_304_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_305_ = lean_int_ediv(v_nano_301_, v___x_304_);
v_millis_306_ = lean_int_add(v___x_303_, v___x_305_);
lean_dec(v___x_305_);
lean_dec(v___x_303_);
return v_millis_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds___boxed(lean_object* v_duration_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Time_Duration_toMilliseconds(v_duration_307_);
lean_dec_ref(v_duration_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds(lean_object* v_duration_309_){
_start:
{
lean_object* v_second_310_; lean_object* v_nano_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_nanos_314_; 
v_second_310_ = lean_ctor_get(v_duration_309_, 0);
v_nano_311_ = lean_ctor_get(v_duration_309_, 1);
v___x_312_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_313_ = lean_int_mul(v_second_310_, v___x_312_);
v_nanos_314_ = lean_int_add(v___x_313_, v_nano_311_);
lean_dec(v___x_313_);
return v_nanos_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds___boxed(lean_object* v_duration_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_Time_Duration_toNanoseconds(v_duration_315_);
lean_dec_ref(v_duration_315_);
return v_res_316_;
}
}
static lean_object* _init_l_Std_Time_Duration_instLE(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Duration_instDecidableLe(lean_object* v_x_318_, lean_object* v_y_319_){
_start:
{
lean_object* v_second_320_; lean_object* v_nano_321_; lean_object* v_second_322_; lean_object* v_nano_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_nanos_326_; lean_object* v___x_327_; lean_object* v_nanos_328_; uint8_t v___x_329_; 
v_second_320_ = lean_ctor_get(v_x_318_, 0);
v_nano_321_ = lean_ctor_get(v_x_318_, 1);
v_second_322_ = lean_ctor_get(v_y_319_, 0);
v_nano_323_ = lean_ctor_get(v_y_319_, 1);
v___x_324_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_325_ = lean_int_mul(v_second_320_, v___x_324_);
v_nanos_326_ = lean_int_add(v___x_325_, v_nano_321_);
lean_dec(v___x_325_);
v___x_327_ = lean_int_mul(v_second_322_, v___x_324_);
v_nanos_328_ = lean_int_add(v___x_327_, v_nano_323_);
lean_dec(v___x_327_);
v___x_329_ = lean_int_dec_le(v_nanos_326_, v_nanos_328_);
lean_dec(v_nanos_328_);
lean_dec(v_nanos_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLe___boxed(lean_object* v_x_330_, lean_object* v_y_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Std_Time_Duration_instDecidableLe(v_x_330_, v_y_331_);
lean_dec_ref(v_y_331_);
lean_dec_ref(v_x_330_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
static lean_object* _init_l_Std_Time_Duration_instLT(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(0);
return v___x_334_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Duration_instDecidableLt(lean_object* v_x_335_, lean_object* v_y_336_){
_start:
{
lean_object* v_second_337_; lean_object* v_nano_338_; lean_object* v_second_339_; lean_object* v_nano_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_nanos_343_; lean_object* v___x_344_; lean_object* v_nanos_345_; uint8_t v___x_346_; 
v_second_337_ = lean_ctor_get(v_x_335_, 0);
v_nano_338_ = lean_ctor_get(v_x_335_, 1);
v_second_339_ = lean_ctor_get(v_y_336_, 0);
v_nano_340_ = lean_ctor_get(v_y_336_, 1);
v___x_341_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_342_ = lean_int_mul(v_second_337_, v___x_341_);
v_nanos_343_ = lean_int_add(v___x_342_, v_nano_338_);
lean_dec(v___x_342_);
v___x_344_ = lean_int_mul(v_second_339_, v___x_341_);
v_nanos_345_ = lean_int_add(v___x_344_, v_nano_340_);
lean_dec(v___x_344_);
v___x_346_ = lean_int_dec_lt(v_nanos_343_, v_nanos_345_);
lean_dec(v_nanos_345_);
lean_dec(v_nanos_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLt___boxed(lean_object* v_x_347_, lean_object* v_y_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_Time_Duration_instDecidableLt(v_x_347_, v_y_348_);
lean_dec_ref(v_y_348_);
lean_dec_ref(v_x_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Std_Time_Duration_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(60u);
v___x_352_ = lean_nat_to_int(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes(lean_object* v_tm_353_){
_start:
{
lean_object* v_second_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_second_354_ = lean_ctor_get(v_tm_353_, 0);
v___x_355_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v___x_356_ = lean_int_div(v_second_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes___boxed(lean_object* v_tm_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Time_Duration_toMinutes(v_tm_357_);
lean_dec_ref(v_tm_357_);
return v_res_358_;
}
}
static lean_object* _init_l_Std_Time_Duration_toDays___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(86400u);
v___x_360_ = lean_nat_to_int(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays(lean_object* v_tm_361_){
_start:
{
lean_object* v_second_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_second_362_ = lean_ctor_get(v_tm_361_, 0);
v___x_363_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v___x_364_ = lean_int_div(v_second_362_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays___boxed(lean_object* v_tm_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Time_Duration_toDays(v_tm_365_);
lean_dec_ref(v_tm_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents(lean_object* v_secs_367_, lean_object* v_nanos_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_369_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_370_ = lean_int_mul(v_secs_367_, v___x_369_);
v___x_371_ = l_Std_Time_Nanosecond_Span_toOffset(v_nanos_368_);
v___x_372_ = lean_int_add(v___x_370_, v___x_371_);
lean_dec(v___x_371_);
lean_dec(v___x_370_);
v___x_373_ = l_Std_Time_Duration_ofNanoseconds(v___x_372_);
lean_dec(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents___boxed(lean_object* v_secs_374_, lean_object* v_nanos_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Time_Duration_fromComponents(v_secs_374_, v_nanos_375_);
lean_dec(v_nanos_375_);
lean_dec(v_secs_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_add(lean_object* v_t_u2081_377_, lean_object* v_t_u2082_378_){
_start:
{
lean_object* v_second_379_; lean_object* v_nano_380_; lean_object* v_second_381_; lean_object* v_nano_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_second_379_ = lean_ctor_get(v_t_u2081_377_, 0);
v_nano_380_ = lean_ctor_get(v_t_u2081_377_, 1);
v_second_381_ = lean_ctor_get(v_t_u2082_378_, 0);
v_nano_382_ = lean_ctor_get(v_t_u2082_378_, 1);
v___x_383_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_384_ = lean_int_mul(v_second_379_, v___x_383_);
v___x_385_ = lean_int_add(v___x_384_, v_nano_380_);
lean_dec(v___x_384_);
v___x_386_ = lean_int_mul(v_second_381_, v___x_383_);
v___x_387_ = lean_int_add(v___x_386_, v_nano_382_);
lean_dec(v___x_386_);
v___x_388_ = lean_int_add(v___x_385_, v___x_387_);
lean_dec(v___x_387_);
lean_dec(v___x_385_);
v___x_389_ = l_Std_Time_Duration_ofNanoseconds(v___x_388_);
lean_dec(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_add___boxed(lean_object* v_t_u2081_390_, lean_object* v_t_u2082_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_Duration_add(v_t_u2081_390_, v_t_u2082_391_);
lean_dec_ref(v_t_u2082_391_);
lean_dec_ref(v_t_u2081_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub(lean_object* v_t_u2081_393_, lean_object* v_t_u2082_394_){
_start:
{
lean_object* v_second_395_; lean_object* v_nano_396_; lean_object* v_second_397_; lean_object* v_nano_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_second_395_ = lean_ctor_get(v_t_u2082_394_, 0);
v_nano_396_ = lean_ctor_get(v_t_u2082_394_, 1);
v_second_397_ = lean_ctor_get(v_t_u2081_393_, 0);
v_nano_398_ = lean_ctor_get(v_t_u2081_393_, 1);
v___x_399_ = lean_int_neg(v_second_395_);
v___x_400_ = lean_int_neg(v_nano_396_);
v___x_401_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_402_ = lean_int_mul(v_second_397_, v___x_401_);
v___x_403_ = lean_int_add(v___x_402_, v_nano_398_);
lean_dec(v___x_402_);
v___x_404_ = lean_int_mul(v___x_399_, v___x_401_);
lean_dec(v___x_399_);
v___x_405_ = lean_int_add(v___x_404_, v___x_400_);
lean_dec(v___x_400_);
lean_dec(v___x_404_);
v___x_406_ = lean_int_add(v___x_403_, v___x_405_);
lean_dec(v___x_405_);
lean_dec(v___x_403_);
v___x_407_ = l_Std_Time_Duration_ofNanoseconds(v___x_406_);
lean_dec(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub___boxed(lean_object* v_t_u2081_408_, lean_object* v_t_u2082_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Time_Duration_sub(v_t_u2081_408_, v_t_u2082_409_);
lean_dec_ref(v_t_u2082_409_);
lean_dec_ref(v_t_u2081_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds(lean_object* v_t_411_, lean_object* v_s_412_){
_start:
{
lean_object* v_second_413_; lean_object* v_nano_414_; lean_object* v___x_415_; lean_object* v_second_416_; lean_object* v_nano_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_second_413_ = lean_ctor_get(v_t_411_, 0);
v_nano_414_ = lean_ctor_get(v_t_411_, 1);
v___x_415_ = l_Std_Time_Duration_ofNanoseconds(v_s_412_);
v_second_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_second_416_);
v_nano_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_nano_417_);
lean_dec_ref(v___x_415_);
v___x_418_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_419_ = lean_int_mul(v_second_413_, v___x_418_);
v___x_420_ = lean_int_add(v___x_419_, v_nano_414_);
lean_dec(v___x_419_);
v___x_421_ = lean_int_mul(v_second_416_, v___x_418_);
lean_dec(v_second_416_);
v___x_422_ = lean_int_add(v___x_421_, v_nano_417_);
lean_dec(v_nano_417_);
lean_dec(v___x_421_);
v___x_423_ = lean_int_add(v___x_420_, v___x_422_);
lean_dec(v___x_422_);
lean_dec(v___x_420_);
v___x_424_ = l_Std_Time_Duration_ofNanoseconds(v___x_423_);
lean_dec(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds___boxed(lean_object* v_t_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Time_Duration_addNanoseconds(v_t_425_, v_s_426_);
lean_dec(v_s_426_);
lean_dec_ref(v_t_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds(lean_object* v_t_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_second_430_; lean_object* v_nano_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_second_435_; lean_object* v_nano_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_second_430_ = lean_ctor_get(v_t_428_, 0);
v_nano_431_ = lean_ctor_get(v_t_428_, 1);
v___x_432_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_433_ = lean_int_mul(v_s_429_, v___x_432_);
v___x_434_ = l_Std_Time_Duration_ofNanoseconds(v___x_433_);
lean_dec(v___x_433_);
v_second_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_second_435_);
v_nano_436_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_nano_436_);
lean_dec_ref(v___x_434_);
v___x_437_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_438_ = lean_int_mul(v_second_430_, v___x_437_);
v___x_439_ = lean_int_add(v___x_438_, v_nano_431_);
lean_dec(v___x_438_);
v___x_440_ = lean_int_mul(v_second_435_, v___x_437_);
lean_dec(v_second_435_);
v___x_441_ = lean_int_add(v___x_440_, v_nano_436_);
lean_dec(v_nano_436_);
lean_dec(v___x_440_);
v___x_442_ = lean_int_add(v___x_439_, v___x_441_);
lean_dec(v___x_441_);
lean_dec(v___x_439_);
v___x_443_ = l_Std_Time_Duration_ofNanoseconds(v___x_442_);
lean_dec(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds___boxed(lean_object* v_t_444_, lean_object* v_s_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Time_Duration_addMilliseconds(v_t_444_, v_s_445_);
lean_dec(v_s_445_);
lean_dec_ref(v_t_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds(lean_object* v_t_447_, lean_object* v_s_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_second_452_; lean_object* v_nano_453_; lean_object* v_second_454_; lean_object* v_nano_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_449_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_450_ = lean_int_mul(v_s_448_, v___x_449_);
v___x_451_ = l_Std_Time_Duration_ofNanoseconds(v___x_450_);
lean_dec(v___x_450_);
v_second_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_second_452_);
v_nano_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_nano_453_);
lean_dec_ref(v___x_451_);
v_second_454_ = lean_ctor_get(v_t_447_, 0);
v_nano_455_ = lean_ctor_get(v_t_447_, 1);
v___x_456_ = lean_int_neg(v_second_452_);
lean_dec(v_second_452_);
v___x_457_ = lean_int_neg(v_nano_453_);
lean_dec(v_nano_453_);
v___x_458_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_459_ = lean_int_mul(v_second_454_, v___x_458_);
v___x_460_ = lean_int_add(v___x_459_, v_nano_455_);
lean_dec(v___x_459_);
v___x_461_ = lean_int_mul(v___x_456_, v___x_458_);
lean_dec(v___x_456_);
v___x_462_ = lean_int_add(v___x_461_, v___x_457_);
lean_dec(v___x_457_);
lean_dec(v___x_461_);
v___x_463_ = lean_int_add(v___x_460_, v___x_462_);
lean_dec(v___x_462_);
lean_dec(v___x_460_);
v___x_464_ = l_Std_Time_Duration_ofNanoseconds(v___x_463_);
lean_dec(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds___boxed(lean_object* v_t_465_, lean_object* v_s_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Time_Duration_subMilliseconds(v_t_465_, v_s_466_);
lean_dec(v_s_466_);
lean_dec_ref(v_t_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds(lean_object* v_t_468_, lean_object* v_s_469_){
_start:
{
lean_object* v___x_470_; lean_object* v_second_471_; lean_object* v_nano_472_; lean_object* v_second_473_; lean_object* v_nano_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_470_ = l_Std_Time_Duration_ofNanoseconds(v_s_469_);
v_second_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_second_471_);
v_nano_472_ = lean_ctor_get(v___x_470_, 1);
lean_inc(v_nano_472_);
lean_dec_ref(v___x_470_);
v_second_473_ = lean_ctor_get(v_t_468_, 0);
v_nano_474_ = lean_ctor_get(v_t_468_, 1);
v___x_475_ = lean_int_neg(v_second_471_);
lean_dec(v_second_471_);
v___x_476_ = lean_int_neg(v_nano_472_);
lean_dec(v_nano_472_);
v___x_477_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_478_ = lean_int_mul(v_second_473_, v___x_477_);
v___x_479_ = lean_int_add(v___x_478_, v_nano_474_);
lean_dec(v___x_478_);
v___x_480_ = lean_int_mul(v___x_475_, v___x_477_);
lean_dec(v___x_475_);
v___x_481_ = lean_int_add(v___x_480_, v___x_476_);
lean_dec(v___x_476_);
lean_dec(v___x_480_);
v___x_482_ = lean_int_add(v___x_479_, v___x_481_);
lean_dec(v___x_481_);
lean_dec(v___x_479_);
v___x_483_ = l_Std_Time_Duration_ofNanoseconds(v___x_482_);
lean_dec(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds___boxed(lean_object* v_t_484_, lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Time_Duration_subNanoseconds(v_t_484_, v_s_485_);
lean_dec(v_s_485_);
lean_dec_ref(v_t_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds(lean_object* v_t_487_, lean_object* v_s_488_){
_start:
{
lean_object* v_second_489_; lean_object* v_nano_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_second_489_ = lean_ctor_get(v_t_487_, 0);
v_nano_490_ = lean_ctor_get(v_t_487_, 1);
v___x_491_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_492_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_493_ = lean_int_mul(v_second_489_, v___x_492_);
v___x_494_ = lean_int_add(v___x_493_, v_nano_490_);
lean_dec(v___x_493_);
v___x_495_ = lean_int_mul(v_s_488_, v___x_492_);
v___x_496_ = lean_int_add(v___x_495_, v___x_491_);
lean_dec(v___x_495_);
v___x_497_ = lean_int_add(v___x_494_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v___x_494_);
v___x_498_ = l_Std_Time_Duration_ofNanoseconds(v___x_497_);
lean_dec(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds___boxed(lean_object* v_t_499_, lean_object* v_s_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Time_Duration_addSeconds(v_t_499_, v_s_500_);
lean_dec(v_s_500_);
lean_dec_ref(v_t_499_);
return v_res_501_;
}
}
static lean_object* _init_l_Std_Time_Duration_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_503_ = lean_int_neg(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds(lean_object* v_t_504_, lean_object* v_s_505_){
_start:
{
lean_object* v_second_506_; lean_object* v_nano_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_second_506_ = lean_ctor_get(v_t_504_, 0);
v_nano_507_ = lean_ctor_get(v_t_504_, 1);
v___x_508_ = lean_int_neg(v_s_505_);
v___x_509_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_510_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_511_ = lean_int_mul(v_second_506_, v___x_510_);
v___x_512_ = lean_int_add(v___x_511_, v_nano_507_);
lean_dec(v___x_511_);
v___x_513_ = lean_int_mul(v___x_508_, v___x_510_);
lean_dec(v___x_508_);
v___x_514_ = lean_int_add(v___x_513_, v___x_509_);
lean_dec(v___x_513_);
v___x_515_ = lean_int_add(v___x_512_, v___x_514_);
lean_dec(v___x_514_);
lean_dec(v___x_512_);
v___x_516_ = l_Std_Time_Duration_ofNanoseconds(v___x_515_);
lean_dec(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds___boxed(lean_object* v_t_517_, lean_object* v_s_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Time_Duration_subSeconds(v_t_517_, v_s_518_);
lean_dec(v_s_518_);
lean_dec_ref(v_t_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes(lean_object* v_t_520_, lean_object* v_m_521_){
_start:
{
lean_object* v_second_522_; lean_object* v_nano_523_; lean_object* v___x_524_; lean_object* v_seconds_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_second_522_ = lean_ctor_get(v_t_520_, 0);
v_nano_523_ = lean_ctor_get(v_t_520_, 1);
v___x_524_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v_seconds_525_ = lean_int_mul(v_m_521_, v___x_524_);
v___x_526_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_527_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_528_ = lean_int_mul(v_second_522_, v___x_527_);
v___x_529_ = lean_int_add(v___x_528_, v_nano_523_);
lean_dec(v___x_528_);
v___x_530_ = lean_int_mul(v_seconds_525_, v___x_527_);
lean_dec(v_seconds_525_);
v___x_531_ = lean_int_add(v___x_530_, v___x_526_);
lean_dec(v___x_530_);
v___x_532_ = lean_int_add(v___x_529_, v___x_531_);
lean_dec(v___x_531_);
lean_dec(v___x_529_);
v___x_533_ = l_Std_Time_Duration_ofNanoseconds(v___x_532_);
lean_dec(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes___boxed(lean_object* v_t_534_, lean_object* v_m_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Time_Duration_addMinutes(v_t_534_, v_m_535_);
lean_dec(v_m_535_);
lean_dec_ref(v_t_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes(lean_object* v_t_537_, lean_object* v_m_538_){
_start:
{
lean_object* v_second_539_; lean_object* v_nano_540_; lean_object* v___x_541_; lean_object* v_seconds_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_second_539_ = lean_ctor_get(v_t_537_, 0);
v_nano_540_ = lean_ctor_get(v_t_537_, 1);
v___x_541_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v_seconds_542_ = lean_int_mul(v_m_538_, v___x_541_);
v___x_543_ = lean_int_neg(v_seconds_542_);
lean_dec(v_seconds_542_);
v___x_544_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_545_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_546_ = lean_int_mul(v_second_539_, v___x_545_);
v___x_547_ = lean_int_add(v___x_546_, v_nano_540_);
lean_dec(v___x_546_);
v___x_548_ = lean_int_mul(v___x_543_, v___x_545_);
lean_dec(v___x_543_);
v___x_549_ = lean_int_add(v___x_548_, v___x_544_);
lean_dec(v___x_548_);
v___x_550_ = lean_int_add(v___x_547_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v___x_547_);
v___x_551_ = l_Std_Time_Duration_ofNanoseconds(v___x_550_);
lean_dec(v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes___boxed(lean_object* v_t_552_, lean_object* v_m_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Time_Duration_subMinutes(v_t_552_, v_m_553_);
lean_dec(v_m_553_);
lean_dec_ref(v_t_552_);
return v_res_554_;
}
}
static lean_object* _init_l_Std_Time_Duration_addHours___closed__0(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(3600u);
v___x_556_ = lean_nat_to_int(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours(lean_object* v_t_557_, lean_object* v_h_558_){
_start:
{
lean_object* v_second_559_; lean_object* v_nano_560_; lean_object* v___x_561_; lean_object* v_seconds_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_second_559_ = lean_ctor_get(v_t_557_, 0);
v_nano_560_ = lean_ctor_get(v_t_557_, 1);
v___x_561_ = lean_obj_once(&l_Std_Time_Duration_addHours___closed__0, &l_Std_Time_Duration_addHours___closed__0_once, _init_l_Std_Time_Duration_addHours___closed__0);
v_seconds_562_ = lean_int_mul(v_h_558_, v___x_561_);
v___x_563_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_564_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_565_ = lean_int_mul(v_second_559_, v___x_564_);
v___x_566_ = lean_int_add(v___x_565_, v_nano_560_);
lean_dec(v___x_565_);
v___x_567_ = lean_int_mul(v_seconds_562_, v___x_564_);
lean_dec(v_seconds_562_);
v___x_568_ = lean_int_add(v___x_567_, v___x_563_);
lean_dec(v___x_567_);
v___x_569_ = lean_int_add(v___x_566_, v___x_568_);
lean_dec(v___x_568_);
lean_dec(v___x_566_);
v___x_570_ = l_Std_Time_Duration_ofNanoseconds(v___x_569_);
lean_dec(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours___boxed(lean_object* v_t_571_, lean_object* v_h_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Time_Duration_addHours(v_t_571_, v_h_572_);
lean_dec(v_h_572_);
lean_dec_ref(v_t_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours(lean_object* v_t_574_, lean_object* v_h_575_){
_start:
{
lean_object* v_second_576_; lean_object* v_nano_577_; lean_object* v___x_578_; lean_object* v_seconds_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_second_576_ = lean_ctor_get(v_t_574_, 0);
v_nano_577_ = lean_ctor_get(v_t_574_, 1);
v___x_578_ = lean_obj_once(&l_Std_Time_Duration_addHours___closed__0, &l_Std_Time_Duration_addHours___closed__0_once, _init_l_Std_Time_Duration_addHours___closed__0);
v_seconds_579_ = lean_int_mul(v_h_575_, v___x_578_);
v___x_580_ = lean_int_neg(v_seconds_579_);
lean_dec(v_seconds_579_);
v___x_581_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_582_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_583_ = lean_int_mul(v_second_576_, v___x_582_);
v___x_584_ = lean_int_add(v___x_583_, v_nano_577_);
lean_dec(v___x_583_);
v___x_585_ = lean_int_mul(v___x_580_, v___x_582_);
lean_dec(v___x_580_);
v___x_586_ = lean_int_add(v___x_585_, v___x_581_);
lean_dec(v___x_585_);
v___x_587_ = lean_int_add(v___x_584_, v___x_586_);
lean_dec(v___x_586_);
lean_dec(v___x_584_);
v___x_588_ = l_Std_Time_Duration_ofNanoseconds(v___x_587_);
lean_dec(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours___boxed(lean_object* v_t_589_, lean_object* v_h_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Time_Duration_subHours(v_t_589_, v_h_590_);
lean_dec(v_h_590_);
lean_dec_ref(v_t_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays(lean_object* v_t_592_, lean_object* v_d_593_){
_start:
{
lean_object* v_second_594_; lean_object* v_nano_595_; lean_object* v___x_596_; lean_object* v_seconds_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_second_594_ = lean_ctor_get(v_t_592_, 0);
v_nano_595_ = lean_ctor_get(v_t_592_, 1);
v___x_596_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v_seconds_597_ = lean_int_mul(v_d_593_, v___x_596_);
v___x_598_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_599_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_600_ = lean_int_mul(v_second_594_, v___x_599_);
v___x_601_ = lean_int_add(v___x_600_, v_nano_595_);
lean_dec(v___x_600_);
v___x_602_ = lean_int_mul(v_seconds_597_, v___x_599_);
lean_dec(v_seconds_597_);
v___x_603_ = lean_int_add(v___x_602_, v___x_598_);
lean_dec(v___x_602_);
v___x_604_ = lean_int_add(v___x_601_, v___x_603_);
lean_dec(v___x_603_);
lean_dec(v___x_601_);
v___x_605_ = l_Std_Time_Duration_ofNanoseconds(v___x_604_);
lean_dec(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays___boxed(lean_object* v_t_606_, lean_object* v_d_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_Time_Duration_addDays(v_t_606_, v_d_607_);
lean_dec(v_d_607_);
lean_dec_ref(v_t_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays(lean_object* v_t_609_, lean_object* v_d_610_){
_start:
{
lean_object* v_second_611_; lean_object* v_nano_612_; lean_object* v___x_613_; lean_object* v_seconds_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_second_611_ = lean_ctor_get(v_t_609_, 0);
v_nano_612_ = lean_ctor_get(v_t_609_, 1);
v___x_613_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v_seconds_614_ = lean_int_mul(v_d_610_, v___x_613_);
v___x_615_ = lean_int_neg(v_seconds_614_);
lean_dec(v_seconds_614_);
v___x_616_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_617_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_618_ = lean_int_mul(v_second_611_, v___x_617_);
v___x_619_ = lean_int_add(v___x_618_, v_nano_612_);
lean_dec(v___x_618_);
v___x_620_ = lean_int_mul(v___x_615_, v___x_617_);
lean_dec(v___x_615_);
v___x_621_ = lean_int_add(v___x_620_, v___x_616_);
lean_dec(v___x_620_);
v___x_622_ = lean_int_add(v___x_619_, v___x_621_);
lean_dec(v___x_621_);
lean_dec(v___x_619_);
v___x_623_ = l_Std_Time_Duration_ofNanoseconds(v___x_622_);
lean_dec(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays___boxed(lean_object* v_t_624_, lean_object* v_d_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Time_Duration_subDays(v_t_624_, v_d_625_);
lean_dec(v_d_625_);
lean_dec_ref(v_t_624_);
return v_res_626_;
}
}
static lean_object* _init_l_Std_Time_Duration_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(604800u);
v___x_628_ = lean_nat_to_int(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks(lean_object* v_t_629_, lean_object* v_w_630_){
_start:
{
lean_object* v_second_631_; lean_object* v_nano_632_; lean_object* v___x_633_; lean_object* v_seconds_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_second_631_ = lean_ctor_get(v_t_629_, 0);
v_nano_632_ = lean_ctor_get(v_t_629_, 1);
v___x_633_ = lean_obj_once(&l_Std_Time_Duration_addWeeks___closed__0, &l_Std_Time_Duration_addWeeks___closed__0_once, _init_l_Std_Time_Duration_addWeeks___closed__0);
v_seconds_634_ = lean_int_mul(v_w_630_, v___x_633_);
v___x_635_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_636_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_637_ = lean_int_mul(v_second_631_, v___x_636_);
v___x_638_ = lean_int_add(v___x_637_, v_nano_632_);
lean_dec(v___x_637_);
v___x_639_ = lean_int_mul(v_seconds_634_, v___x_636_);
lean_dec(v_seconds_634_);
v___x_640_ = lean_int_add(v___x_639_, v___x_635_);
lean_dec(v___x_639_);
v___x_641_ = lean_int_add(v___x_638_, v___x_640_);
lean_dec(v___x_640_);
lean_dec(v___x_638_);
v___x_642_ = l_Std_Time_Duration_ofNanoseconds(v___x_641_);
lean_dec(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks___boxed(lean_object* v_t_643_, lean_object* v_w_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Time_Duration_addWeeks(v_t_643_, v_w_644_);
lean_dec(v_w_644_);
lean_dec_ref(v_t_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks(lean_object* v_t_646_, lean_object* v_w_647_){
_start:
{
lean_object* v_second_648_; lean_object* v_nano_649_; lean_object* v___x_650_; lean_object* v_seconds_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_second_648_ = lean_ctor_get(v_t_646_, 0);
v_nano_649_ = lean_ctor_get(v_t_646_, 1);
v___x_650_ = lean_obj_once(&l_Std_Time_Duration_addWeeks___closed__0, &l_Std_Time_Duration_addWeeks___closed__0_once, _init_l_Std_Time_Duration_addWeeks___closed__0);
v_seconds_651_ = lean_int_mul(v_w_647_, v___x_650_);
v___x_652_ = lean_int_neg(v_seconds_651_);
lean_dec(v_seconds_651_);
v___x_653_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_654_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_655_ = lean_int_mul(v_second_648_, v___x_654_);
v___x_656_ = lean_int_add(v___x_655_, v_nano_649_);
lean_dec(v___x_655_);
v___x_657_ = lean_int_mul(v___x_652_, v___x_654_);
lean_dec(v___x_652_);
v___x_658_ = lean_int_add(v___x_657_, v___x_653_);
lean_dec(v___x_657_);
v___x_659_ = lean_int_add(v___x_656_, v___x_658_);
lean_dec(v___x_658_);
lean_dec(v___x_656_);
v___x_660_ = l_Std_Time_Duration_ofNanoseconds(v___x_659_);
lean_dec(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks___boxed(lean_object* v_t_661_, lean_object* v_w_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Time_Duration_subWeeks(v_t_661_, v_w_662_);
lean_dec(v_w_662_);
lean_dec_ref(v_t_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0(lean_object* v_i_723_, lean_object* v_d_724_){
_start:
{
lean_object* v_second_725_; lean_object* v_nano_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_second_725_ = lean_ctor_get(v_d_724_, 0);
v_nano_726_ = lean_ctor_get(v_d_724_, 1);
v___x_727_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_728_ = lean_int_mul(v_second_725_, v___x_727_);
v___x_729_ = lean_int_add(v___x_728_, v_nano_726_);
lean_dec(v___x_728_);
v___x_730_ = lean_int_mul(v___x_729_, v_i_723_);
lean_dec(v___x_729_);
v___x_731_ = l_Std_Time_Duration_ofNanoseconds(v___x_730_);
lean_dec(v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0___boxed(lean_object* v_i_732_, lean_object* v_d_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_Time_Duration_instHMulInt___lam__0(v_i_732_, v_d_733_);
lean_dec_ref(v_d_733_);
lean_dec(v_i_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0(lean_object* v_d_737_, lean_object* v_i_738_){
_start:
{
lean_object* v_second_739_; lean_object* v_nano_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_second_739_ = lean_ctor_get(v_d_737_, 0);
v_nano_740_ = lean_ctor_get(v_d_737_, 1);
v___x_741_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_742_ = lean_int_mul(v_second_739_, v___x_741_);
v___x_743_ = lean_int_add(v___x_742_, v_nano_740_);
lean_dec(v___x_742_);
v___x_744_ = lean_int_mul(v___x_743_, v_i_738_);
lean_dec(v___x_743_);
v___x_745_ = l_Std_Time_Duration_ofNanoseconds(v___x_744_);
lean_dec(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0___boxed(lean_object* v_d_746_, lean_object* v_i_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_Time_Duration_instHMulInt__1___lam__0(v_d_746_, v_i_747_);
lean_dec(v_i_747_);
lean_dec_ref(v_d_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0(lean_object* v_pt_751_, lean_object* v_d_752_){
_start:
{
lean_object* v_second_753_; lean_object* v_nano_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_second_753_ = lean_ctor_get(v_d_752_, 0);
v_nano_754_ = lean_ctor_get(v_d_752_, 1);
v___x_755_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_756_ = lean_int_mul(v_second_753_, v___x_755_);
v___x_757_ = lean_int_add(v___x_756_, v_nano_754_);
lean_dec(v___x_756_);
v___x_758_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_751_);
v___x_759_ = lean_int_add(v___x_757_, v___x_758_);
lean_dec(v___x_758_);
lean_dec(v___x_757_);
v___x_760_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_759_);
lean_dec(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed(lean_object* v_pt_761_, lean_object* v_d_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Time_Duration_instHAddPlainTime___lam__0(v_pt_761_, v_d_762_);
lean_dec_ref(v_d_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0(lean_object* v_pt_766_, lean_object* v_d_767_){
_start:
{
lean_object* v_second_768_; lean_object* v_nano_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_second_768_ = lean_ctor_get(v_d_767_, 0);
v_nano_769_ = lean_ctor_get(v_d_767_, 1);
v___x_770_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_766_);
v___x_771_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_772_ = lean_int_mul(v_second_768_, v___x_771_);
v___x_773_ = lean_int_add(v___x_772_, v_nano_769_);
lean_dec(v___x_772_);
v___x_774_ = lean_int_sub(v___x_770_, v___x_773_);
lean_dec(v___x_773_);
lean_dec(v___x_770_);
v___x_775_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_774_);
lean_dec(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed(lean_object* v_pt_776_, lean_object* v_d_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_Time_Duration_instHSubPlainTime___lam__0(v_pt_776_, v_d_777_);
lean_dec_ref(v_d_777_);
return v_res_778_;
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
