// Lean compiler output
// Module: Std.Time.Duration
// Imports: public import Std.Time.Date public import Init.Data.String.Basic public import Init.Data.String.Length
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
lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object*);
lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Time_Hour_Offset_toSeconds___boxed(lean_object*);
lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object*);
lean_object* l_Std_Time_Second_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Minute_Offset_toSeconds___boxed(lean_object*);
lean_object* l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Time_instOrdDuration___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdDuration___closed__2 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__2_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdDuration___closed__3 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__3_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdDuration___closed__2_value),((lean_object*)&l_Std_Time_instOrdDuration___closed__0_value)} };
static const lean_object* l_Std_Time_instOrdDuration___closed__4 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__4_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdDuration___closed__3_value),((lean_object*)&l_Std_Time_instOrdDuration___closed__1_value)} };
static const lean_object* l_Std_Time_instOrdDuration___closed__5 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__5_value;
static const lean_closure_object l_Std_Time_instOrdDuration___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareLex___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdDuration___closed__4_value),((lean_object*)&l_Std_Time_instOrdDuration___closed__5_value)} };
static const lean_object* l_Std_Time_instOrdDuration___closed__6 = (const lean_object*)&l_Std_Time_instOrdDuration___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_instOrdDuration = (const lean_object*)&l_Std_Time_instOrdDuration___closed__6_value;
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
v___x_51_ = l_Std_Time_Second_instReprOffset___lam__0(v_second_42_, v___x_50_);
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
v___x_65_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nano_43_, v___x_50_);
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
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object* v_x_93_, lean_object* v_x_94_){
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
LEAN_EXPORT void l_Std_Time_instDecidableEqDuration_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_93_ = stack[0].m_obj;
lean_object* v_x_94_ = stack[1].m_obj;
uint8_t v_res_101_;
v_res_101_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_93_, v_x_94_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqDuration_decEq___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_102_, v_x_103_);
lean_dec_ref(v_x_103_);
lean_dec_ref(v_x_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint8_t l_Std_Time_instDecidableEqDuration(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_106_, v_x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqDuration_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_106_ = stack[0].m_obj;
lean_object* v_x_107_ = stack[1].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_Std_Time_instDecidableEqDuration(v_x_106_, v_x_107_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqDuration___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Std_Time_instDecidableEqDuration(v_x_110_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec_ref(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_zero_116_; uint8_t v_isZero_117_; 
v_zero_116_ = lean_unsigned_to_nat(0u);
v_isZero_117_ = lean_nat_dec_eq(v_x_114_, v_zero_116_);
if (v_isZero_117_ == 1)
{
lean_dec(v_x_114_);
return v_x_115_;
}
else
{
uint32_t v___x_118_; lean_object* v_one_119_; lean_object* v_n_120_; lean_object* v___x_121_; 
v___x_118_ = 48;
v_one_119_ = lean_unsigned_to_nat(1u);
v_n_120_ = lean_nat_sub(v_x_114_, v_one_119_);
lean_dec(v_x_114_);
v___x_121_ = lean_string_push(v_x_115_, v___x_118_);
v_x_114_ = v_n_120_;
v_x_115_ = v___x_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration_leftPad(lean_object* v_n_124_, lean_object* v_s_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___x_127_ = lean_string_length(v_s_125_);
v___x_128_ = lean_nat_sub(v_n_124_, v___x_127_);
v___x_129_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(v___x_128_, v___x_126_);
v___x_130_ = lean_string_append(v___x_129_, v_s_125_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration_leftPad___boxed(lean_object* v_n_131_, lean_object* v_s_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Time_instToStringDuration_leftPad(v_n_131_, v_s_132_);
lean_dec_ref(v_s_132_);
lean_dec(v_n_131_);
return v_res_133_;
}
}
static lean_object* _init_l_Std_Time_instToStringDuration___lam__0___closed__1(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_nat_to_int(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringDuration___lam__0(lean_object* v_s_139_){
_start:
{
lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v_second_146_; lean_object* v_nano_147_; lean_object* v_fst_149_; lean_object* v_fst_150_; lean_object* v_snd_151_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_second_146_ = lean_ctor_get(v_s_139_, 0);
lean_inc(v_second_146_);
v_nano_147_ = lean_ctor_get(v_s_139_, 1);
lean_inc(v_nano_147_);
lean_dec_ref(v_s_139_);
v___x_162_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_163_ = lean_int_dec_lt(v___x_162_, v_second_146_);
if (v___x_163_ == 0)
{
uint8_t v___x_164_; 
v___x_164_ = lean_int_dec_lt(v_second_146_, v___x_162_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
v___x_165_ = lean_int_dec_lt(v_nano_147_, v___x_162_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_147_);
v_fst_149_ = v___x_166_;
v_fst_150_ = v_second_146_;
v_snd_151_ = v_nano_147_;
goto v___jp_148_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_168_ = lean_int_neg(v_second_146_);
lean_dec(v_second_146_);
v___x_169_ = lean_int_neg(v_nano_147_);
v_fst_149_ = v___x_167_;
v_fst_150_ = v___x_168_;
v_snd_151_ = v___x_169_;
goto v___jp_148_;
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_171_ = lean_int_neg(v_second_146_);
lean_dec(v_second_146_);
v___x_172_ = lean_int_neg(v_nano_147_);
v_fst_149_ = v___x_170_;
v_fst_150_ = v___x_171_;
v_snd_151_ = v___x_172_;
goto v___jp_148_;
}
}
else
{
lean_object* v___x_173_; 
v___x_173_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_147_);
v_fst_149_ = v___x_173_;
v_fst_150_ = v_second_146_;
v_snd_151_ = v_nano_147_;
goto v___jp_148_;
}
v___jp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_string_append(v___y_141_, v___y_142_);
lean_dec_ref(v___y_142_);
v___x_144_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__0));
v___x_145_ = lean_string_append(v___x_143_, v___x_144_);
return v___x_145_;
}
v___jp_148_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = l_Int_repr(v_fst_150_);
lean_dec(v_fst_150_);
lean_inc_ref(v_fst_149_);
v___x_153_ = lean_string_append(v_fst_149_, v___x_152_);
lean_dec_ref(v___x_152_);
v___x_154_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_155_ = lean_int_dec_eq(v_nano_147_, v___x_154_);
lean_dec(v_nano_147_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__2));
v___x_157_ = lean_unsigned_to_nat(9u);
v___x_158_ = l_Int_repr(v_snd_151_);
lean_dec(v_snd_151_);
v___x_159_ = l_Std_Time_instToStringDuration_leftPad(v___x_157_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = lean_string_append(v___x_156_, v___x_159_);
lean_dec_ref(v___x_159_);
v___y_141_ = v___x_153_;
v___y_142_ = v___x_160_;
goto v___jp_140_;
}
else
{
lean_object* v___x_161_; 
lean_dec(v_snd_151_);
v___x_161_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___y_141_ = v___x_153_;
v___y_142_ = v___x_161_;
goto v___jp_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0(lean_object* v_s_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v_second_186_; lean_object* v_nano_187_; lean_object* v_fst_189_; lean_object* v_fst_190_; lean_object* v_snd_191_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_second_186_ = lean_ctor_get(v_s_176_, 0);
lean_inc(v_second_186_);
v_nano_187_ = lean_ctor_get(v_s_176_, 1);
lean_inc(v_nano_187_);
lean_dec_ref(v_s_176_);
v___x_202_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_203_ = lean_int_dec_lt(v___x_202_, v_second_186_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
v___x_204_ = lean_int_dec_lt(v_second_186_, v___x_202_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = lean_int_dec_lt(v_nano_187_, v___x_202_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_187_);
v_fst_189_ = v___x_206_;
v_fst_190_ = v_second_186_;
v_snd_191_ = v_nano_187_;
goto v___jp_188_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_208_ = lean_int_neg(v_second_186_);
lean_dec(v_second_186_);
v___x_209_ = lean_int_neg(v_nano_187_);
v_fst_189_ = v___x_207_;
v_fst_190_ = v___x_208_;
v_snd_191_ = v___x_209_;
goto v___jp_188_;
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__3));
v___x_211_ = lean_int_neg(v_second_186_);
lean_dec(v_second_186_);
v___x_212_ = lean_int_neg(v_nano_187_);
v_fst_189_ = v___x_210_;
v_fst_190_ = v___x_211_;
v_snd_191_ = v___x_212_;
goto v___jp_188_;
}
}
else
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
lean_inc(v_nano_187_);
v_fst_189_ = v___x_213_;
v_fst_190_ = v_second_186_;
v_snd_191_ = v_nano_187_;
goto v___jp_188_;
}
v___jp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_181_ = lean_string_append(v___y_179_, v___y_180_);
lean_dec_ref(v___y_180_);
v___x_182_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__0));
v___x_183_ = lean_string_append(v___x_181_, v___x_182_);
v___x_184_ = l_String_quote(v___x_183_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
v___jp_188_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_192_ = l_Int_repr(v_fst_190_);
lean_dec(v_fst_190_);
lean_inc_ref(v_fst_189_);
v___x_193_ = lean_string_append(v_fst_189_, v___x_192_);
lean_dec_ref(v___x_192_);
v___x_194_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_195_ = lean_int_dec_eq(v_nano_187_, v___x_194_);
lean_dec(v_nano_187_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Std_Time_instToStringDuration___lam__0___closed__2));
v___x_197_ = lean_unsigned_to_nat(9u);
v___x_198_ = l_Int_repr(v_snd_191_);
lean_dec(v_snd_191_);
v___x_199_ = l_Std_Time_instToStringDuration_leftPad(v___x_197_, v___x_198_);
lean_dec_ref(v___x_198_);
v___x_200_ = lean_string_append(v___x_196_, v___x_199_);
lean_dec_ref(v___x_199_);
v___y_179_ = v___x_193_;
v___y_180_ = v___x_200_;
goto v___jp_178_;
}
else
{
lean_object* v___x_201_; 
lean_dec(v_snd_191_);
v___x_201_ = ((lean_object*)(l_Std_Time_instToStringDuration_leftPad___closed__0));
v___y_179_ = v___x_193_;
v___y_180_ = v___x_201_;
goto v___jp_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDuration__1___lam__0___boxed(lean_object* v_s_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_Time_instReprDuration__1___lam__0(v_s_214_, v___y_215_);
lean_dec(v___y_215_);
return v_res_216_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration___closed__0(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Std_Time_instInhabitedDuration___closed__0, &l_Std_Time_instInhabitedDuration___closed__0_once, _init_l_Std_Time_instInhabitedDuration___closed__0);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDuration(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Std_Time_instInhabitedDuration___closed__1, &l_Std_Time_instInhabitedDuration___closed__1_once, _init_l_Std_Time_instInhabitedDuration___closed__1);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOfNatDuration(lean_object* v_n_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_nat_to_int(v_n_224_);
v___x_226_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0(lean_object* v_x_228_){
_start:
{
lean_object* v_second_229_; 
v_second_229_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_second_229_);
return v_second_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__0___boxed(lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Time_instOrdDuration___lam__0(v_x_230_);
lean_dec_ref(v_x_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1(lean_object* v_x_232_){
_start:
{
lean_object* v_nano_233_; 
v_nano_233_ = lean_ctor_get(v_x_232_, 1);
lean_inc(v_nano_233_);
return v_nano_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDuration___lam__1___boxed(lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Time_instOrdDuration___lam__1(v_x_234_);
lean_dec_ref(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_neg(lean_object* v_duration_250_){
_start:
{
lean_object* v_second_251_; lean_object* v_nano_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_261_; 
v_second_251_ = lean_ctor_get(v_duration_250_, 0);
v_nano_252_ = lean_ctor_get(v_duration_250_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_duration_250_);
if (v_isSharedCheck_261_ == 0)
{
v___x_254_ = v_duration_250_;
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_nano_252_);
lean_inc(v_second_251_);
lean_dec(v_duration_250_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_int_neg(v_second_251_);
lean_dec(v_second_251_);
v___x_257_ = lean_int_neg(v_nano_252_);
lean_dec(v_nano_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_257_);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofSeconds(lean_object* v_s_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_s_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Duration_ofNanoseconds_spec__1(lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Rat_ofInt(v_a_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Std_Time_Duration_ofNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1000000000u);
v___x_268_ = lean_nat_to_int(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object* v_s_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_271_ = lean_int_div(v_s_269_, v___x_270_);
v___x_272_ = lean_int_mod(v_s_269_, v___x_270_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofNanoseconds___boxed(lean_object* v_s_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Time_Duration_ofNanoseconds(v_s_274_);
lean_dec(v_s_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Duration_ofNanoseconds_spec__0(lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_nat_to_int(v_a_276_);
v___x_278_ = l_Rat_ofInt(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Time_Duration_ofMillisecond___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1000000u);
v___x_280_ = lean_nat_to_int(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond(lean_object* v_s_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_283_ = lean_int_mul(v_s_281_, v___x_282_);
v___x_284_ = l_Std_Time_Duration_ofNanoseconds(v___x_283_);
lean_dec(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_ofMillisecond___boxed(lean_object* v_s_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Time_Duration_ofMillisecond(v_s_285_);
lean_dec(v_s_285_);
return v_res_286_;
}
}
uint8_t l_Std_Time_Duration_isZero(lean_object* v_d_287_){
_start:
{
lean_object* v_second_288_; lean_object* v_nano_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_second_288_ = lean_ctor_get(v_d_287_, 0);
v_nano_289_ = lean_ctor_get(v_d_287_, 1);
v___x_290_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_291_ = lean_int_dec_eq(v_second_288_, v___x_290_);
if (v___x_291_ == 0)
{
return v___x_291_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = lean_int_dec_eq(v_nano_289_, v___x_290_);
return v___x_292_;
}
}
}
LEAN_EXPORT void l_Std_Time_Duration_isZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_287_ = stack[0].m_obj;
uint8_t v_res_293_;
v_res_293_ = l_Std_Time_Duration_isZero(v_d_287_);
stack->m_num = v_res_293_;
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_isZero___boxed(lean_object* v_d_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_Time_Duration_isZero(v_d_294_);
lean_dec_ref(v_d_294_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds(lean_object* v_duration_297_){
_start:
{
lean_object* v_second_298_; 
v_second_298_ = lean_ctor_get(v_duration_297_, 0);
lean_inc(v_second_298_);
return v_second_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toSeconds___boxed(lean_object* v_duration_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Time_Duration_toSeconds(v_duration_299_);
lean_dec_ref(v_duration_299_);
return v_res_300_;
}
}
static lean_object* _init_l_Std_Time_Duration_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1000u);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds(lean_object* v_duration_303_){
_start:
{
lean_object* v_second_304_; lean_object* v_nano_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_millis_310_; 
v_second_304_ = lean_ctor_get(v_duration_303_, 0);
v_nano_305_ = lean_ctor_get(v_duration_303_, 1);
v___x_306_ = lean_obj_once(&l_Std_Time_Duration_toMilliseconds___closed__0, &l_Std_Time_Duration_toMilliseconds___closed__0_once, _init_l_Std_Time_Duration_toMilliseconds___closed__0);
v___x_307_ = lean_int_mul(v_second_304_, v___x_306_);
v___x_308_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_309_ = lean_int_ediv(v_nano_305_, v___x_308_);
v_millis_310_ = lean_int_add(v___x_307_, v___x_309_);
lean_dec(v___x_309_);
lean_dec(v___x_307_);
return v_millis_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMilliseconds___boxed(lean_object* v_duration_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Time_Duration_toMilliseconds(v_duration_311_);
lean_dec_ref(v_duration_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds(lean_object* v_duration_313_){
_start:
{
lean_object* v_second_314_; lean_object* v_nano_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_nanos_318_; 
v_second_314_ = lean_ctor_get(v_duration_313_, 0);
v_nano_315_ = lean_ctor_get(v_duration_313_, 1);
v___x_316_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_317_ = lean_int_mul(v_second_314_, v___x_316_);
v_nanos_318_ = lean_int_add(v___x_317_, v_nano_315_);
lean_dec(v___x_317_);
return v_nanos_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toNanoseconds___boxed(lean_object* v_duration_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Time_Duration_toNanoseconds(v_duration_319_);
lean_dec_ref(v_duration_319_);
return v_res_320_;
}
}
static lean_object* _init_l_Std_Time_Duration_instLE(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
uint8_t l_Std_Time_Duration_instDecidableLe(lean_object* v_x_322_, lean_object* v_y_323_){
_start:
{
lean_object* v_second_324_; lean_object* v_nano_325_; lean_object* v_second_326_; lean_object* v_nano_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_nanos_330_; lean_object* v___x_331_; lean_object* v_nanos_332_; uint8_t v___x_333_; 
v_second_324_ = lean_ctor_get(v_x_322_, 0);
v_nano_325_ = lean_ctor_get(v_x_322_, 1);
v_second_326_ = lean_ctor_get(v_y_323_, 0);
v_nano_327_ = lean_ctor_get(v_y_323_, 1);
v___x_328_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_329_ = lean_int_mul(v_second_324_, v___x_328_);
v_nanos_330_ = lean_int_add(v___x_329_, v_nano_325_);
lean_dec(v___x_329_);
v___x_331_ = lean_int_mul(v_second_326_, v___x_328_);
v_nanos_332_ = lean_int_add(v___x_331_, v_nano_327_);
lean_dec(v___x_331_);
v___x_333_ = lean_int_dec_le(v_nanos_330_, v_nanos_332_);
lean_dec(v_nanos_332_);
lean_dec(v_nanos_330_);
return v___x_333_;
}
}
LEAN_EXPORT void l_Std_Time_Duration_instDecidableLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_322_ = stack[0].m_obj;
lean_object* v_y_323_ = stack[1].m_obj;
uint8_t v_res_334_;
v_res_334_ = l_Std_Time_Duration_instDecidableLe(v_x_322_, v_y_323_);
stack->m_num = v_res_334_;
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLe___boxed(lean_object* v_x_335_, lean_object* v_y_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_Time_Duration_instDecidableLe(v_x_335_, v_y_336_);
lean_dec_ref(v_y_336_);
lean_dec_ref(v_x_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
static lean_object* _init_l_Std_Time_Duration_instLT(void){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
}
uint8_t l_Std_Time_Duration_instDecidableLt(lean_object* v_x_340_, lean_object* v_y_341_){
_start:
{
lean_object* v_second_342_; lean_object* v_nano_343_; lean_object* v_second_344_; lean_object* v_nano_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_nanos_348_; lean_object* v___x_349_; lean_object* v_nanos_350_; uint8_t v___x_351_; 
v_second_342_ = lean_ctor_get(v_x_340_, 0);
v_nano_343_ = lean_ctor_get(v_x_340_, 1);
v_second_344_ = lean_ctor_get(v_y_341_, 0);
v_nano_345_ = lean_ctor_get(v_y_341_, 1);
v___x_346_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_347_ = lean_int_mul(v_second_342_, v___x_346_);
v_nanos_348_ = lean_int_add(v___x_347_, v_nano_343_);
lean_dec(v___x_347_);
v___x_349_ = lean_int_mul(v_second_344_, v___x_346_);
v_nanos_350_ = lean_int_add(v___x_349_, v_nano_345_);
lean_dec(v___x_349_);
v___x_351_ = lean_int_dec_lt(v_nanos_348_, v_nanos_350_);
lean_dec(v_nanos_350_);
lean_dec(v_nanos_348_);
return v___x_351_;
}
}
LEAN_EXPORT void l_Std_Time_Duration_instDecidableLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_340_ = stack[0].m_obj;
lean_object* v_y_341_ = stack[1].m_obj;
uint8_t v_res_352_;
v_res_352_ = l_Std_Time_Duration_instDecidableLt(v_x_340_, v_y_341_);
stack->m_num = v_res_352_;
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instDecidableLt___boxed(lean_object* v_x_353_, lean_object* v_y_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Std_Time_Duration_instDecidableLt(v_x_353_, v_y_354_);
lean_dec_ref(v_y_354_);
lean_dec_ref(v_x_353_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
static lean_object* _init_l_Std_Time_Duration_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(60u);
v___x_358_ = lean_nat_to_int(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes(lean_object* v_tm_359_){
_start:
{
lean_object* v_second_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_second_360_ = lean_ctor_get(v_tm_359_, 0);
v___x_361_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v___x_362_ = lean_int_div(v_second_360_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toMinutes___boxed(lean_object* v_tm_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Time_Duration_toMinutes(v_tm_363_);
lean_dec_ref(v_tm_363_);
return v_res_364_;
}
}
static lean_object* _init_l_Std_Time_Duration_toDays___closed__0(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(86400u);
v___x_366_ = lean_nat_to_int(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays(lean_object* v_tm_367_){
_start:
{
lean_object* v_second_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_second_368_ = lean_ctor_get(v_tm_367_, 0);
v___x_369_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v___x_370_ = lean_int_div(v_second_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_toDays___boxed(lean_object* v_tm_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Time_Duration_toDays(v_tm_371_);
lean_dec_ref(v_tm_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents(lean_object* v_secs_373_, lean_object* v_nanos_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_375_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_376_ = lean_int_mul(v_secs_373_, v___x_375_);
v___x_377_ = l_Std_Time_Nanosecond_Span_toOffset(v_nanos_374_);
v___x_378_ = lean_int_add(v___x_376_, v___x_377_);
lean_dec(v___x_377_);
lean_dec(v___x_376_);
v___x_379_ = l_Std_Time_Duration_ofNanoseconds(v___x_378_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_fromComponents___boxed(lean_object* v_secs_380_, lean_object* v_nanos_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Time_Duration_fromComponents(v_secs_380_, v_nanos_381_);
lean_dec(v_nanos_381_);
lean_dec(v_secs_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_add(lean_object* v_t_u2081_383_, lean_object* v_t_u2082_384_){
_start:
{
lean_object* v_second_385_; lean_object* v_nano_386_; lean_object* v_second_387_; lean_object* v_nano_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_nanos_391_; lean_object* v___x_392_; lean_object* v_nanos_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_second_385_ = lean_ctor_get(v_t_u2081_383_, 0);
v_nano_386_ = lean_ctor_get(v_t_u2081_383_, 1);
v_second_387_ = lean_ctor_get(v_t_u2082_384_, 0);
v_nano_388_ = lean_ctor_get(v_t_u2082_384_, 1);
v___x_389_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_390_ = lean_int_mul(v_second_385_, v___x_389_);
v_nanos_391_ = lean_int_add(v___x_390_, v_nano_386_);
lean_dec(v___x_390_);
v___x_392_ = lean_int_mul(v_second_387_, v___x_389_);
v_nanos_393_ = lean_int_add(v___x_392_, v_nano_388_);
lean_dec(v___x_392_);
v___x_394_ = lean_int_add(v_nanos_391_, v_nanos_393_);
lean_dec(v_nanos_393_);
lean_dec(v_nanos_391_);
v___x_395_ = l_Std_Time_Duration_ofNanoseconds(v___x_394_);
lean_dec(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_add___boxed(lean_object* v_t_u2081_396_, lean_object* v_t_u2082_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_Time_Duration_add(v_t_u2081_396_, v_t_u2082_397_);
lean_dec_ref(v_t_u2082_397_);
lean_dec_ref(v_t_u2081_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub(lean_object* v_t_u2081_399_, lean_object* v_t_u2082_400_){
_start:
{
lean_object* v_second_401_; lean_object* v_nano_402_; lean_object* v_second_403_; lean_object* v_nano_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_nanos_409_; lean_object* v___x_410_; lean_object* v_nanos_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_second_401_ = lean_ctor_get(v_t_u2082_400_, 0);
v_nano_402_ = lean_ctor_get(v_t_u2082_400_, 1);
v_second_403_ = lean_ctor_get(v_t_u2081_399_, 0);
v_nano_404_ = lean_ctor_get(v_t_u2081_399_, 1);
v___x_405_ = lean_int_neg(v_second_401_);
v___x_406_ = lean_int_neg(v_nano_402_);
v___x_407_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_408_ = lean_int_mul(v_second_403_, v___x_407_);
v_nanos_409_ = lean_int_add(v___x_408_, v_nano_404_);
lean_dec(v___x_408_);
v___x_410_ = lean_int_mul(v___x_405_, v___x_407_);
lean_dec(v___x_405_);
v_nanos_411_ = lean_int_add(v___x_410_, v___x_406_);
lean_dec(v___x_406_);
lean_dec(v___x_410_);
v___x_412_ = lean_int_add(v_nanos_409_, v_nanos_411_);
lean_dec(v_nanos_411_);
lean_dec(v_nanos_409_);
v___x_413_ = l_Std_Time_Duration_ofNanoseconds(v___x_412_);
lean_dec(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_sub___boxed(lean_object* v_t_u2081_414_, lean_object* v_t_u2082_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Time_Duration_sub(v_t_u2081_414_, v_t_u2082_415_);
lean_dec_ref(v_t_u2082_415_);
lean_dec_ref(v_t_u2081_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds(lean_object* v_t_417_, lean_object* v_s_418_){
_start:
{
lean_object* v_second_419_; lean_object* v_nano_420_; lean_object* v___x_421_; lean_object* v_second_422_; lean_object* v_nano_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_nanos_426_; lean_object* v___x_427_; lean_object* v_nanos_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_second_419_ = lean_ctor_get(v_t_417_, 0);
v_nano_420_ = lean_ctor_get(v_t_417_, 1);
v___x_421_ = l_Std_Time_Duration_ofNanoseconds(v_s_418_);
v_second_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_second_422_);
v_nano_423_ = lean_ctor_get(v___x_421_, 1);
lean_inc(v_nano_423_);
lean_dec_ref(v___x_421_);
v___x_424_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_425_ = lean_int_mul(v_second_419_, v___x_424_);
v_nanos_426_ = lean_int_add(v___x_425_, v_nano_420_);
lean_dec(v___x_425_);
v___x_427_ = lean_int_mul(v_second_422_, v___x_424_);
lean_dec(v_second_422_);
v_nanos_428_ = lean_int_add(v___x_427_, v_nano_423_);
lean_dec(v_nano_423_);
lean_dec(v___x_427_);
v___x_429_ = lean_int_add(v_nanos_426_, v_nanos_428_);
lean_dec(v_nanos_428_);
lean_dec(v_nanos_426_);
v___x_430_ = l_Std_Time_Duration_ofNanoseconds(v___x_429_);
lean_dec(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addNanoseconds___boxed(lean_object* v_t_431_, lean_object* v_s_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Time_Duration_addNanoseconds(v_t_431_, v_s_432_);
lean_dec(v_s_432_);
lean_dec_ref(v_t_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds(lean_object* v_t_434_, lean_object* v_s_435_){
_start:
{
lean_object* v_second_436_; lean_object* v_nano_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_second_441_; lean_object* v_nano_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_nanos_445_; lean_object* v___x_446_; lean_object* v_nanos_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_second_436_ = lean_ctor_get(v_t_434_, 0);
v_nano_437_ = lean_ctor_get(v_t_434_, 1);
v___x_438_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_439_ = lean_int_mul(v_s_435_, v___x_438_);
v___x_440_ = l_Std_Time_Duration_ofNanoseconds(v___x_439_);
lean_dec(v___x_439_);
v_second_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_second_441_);
v_nano_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_nano_442_);
lean_dec_ref(v___x_440_);
v___x_443_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_444_ = lean_int_mul(v_second_436_, v___x_443_);
v_nanos_445_ = lean_int_add(v___x_444_, v_nano_437_);
lean_dec(v___x_444_);
v___x_446_ = lean_int_mul(v_second_441_, v___x_443_);
lean_dec(v_second_441_);
v_nanos_447_ = lean_int_add(v___x_446_, v_nano_442_);
lean_dec(v_nano_442_);
lean_dec(v___x_446_);
v___x_448_ = lean_int_add(v_nanos_445_, v_nanos_447_);
lean_dec(v_nanos_447_);
lean_dec(v_nanos_445_);
v___x_449_ = l_Std_Time_Duration_ofNanoseconds(v___x_448_);
lean_dec(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMilliseconds___boxed(lean_object* v_t_450_, lean_object* v_s_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_Time_Duration_addMilliseconds(v_t_450_, v_s_451_);
lean_dec(v_s_451_);
lean_dec_ref(v_t_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds(lean_object* v_t_453_, lean_object* v_s_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v_second_458_; lean_object* v_nano_459_; lean_object* v_second_460_; lean_object* v_nano_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_nanos_466_; lean_object* v___x_467_; lean_object* v_nanos_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_455_ = lean_obj_once(&l_Std_Time_Duration_ofMillisecond___closed__0, &l_Std_Time_Duration_ofMillisecond___closed__0_once, _init_l_Std_Time_Duration_ofMillisecond___closed__0);
v___x_456_ = lean_int_mul(v_s_454_, v___x_455_);
v___x_457_ = l_Std_Time_Duration_ofNanoseconds(v___x_456_);
lean_dec(v___x_456_);
v_second_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_second_458_);
v_nano_459_ = lean_ctor_get(v___x_457_, 1);
lean_inc(v_nano_459_);
lean_dec_ref(v___x_457_);
v_second_460_ = lean_ctor_get(v_t_453_, 0);
v_nano_461_ = lean_ctor_get(v_t_453_, 1);
v___x_462_ = lean_int_neg(v_second_458_);
lean_dec(v_second_458_);
v___x_463_ = lean_int_neg(v_nano_459_);
lean_dec(v_nano_459_);
v___x_464_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_465_ = lean_int_mul(v_second_460_, v___x_464_);
v_nanos_466_ = lean_int_add(v___x_465_, v_nano_461_);
lean_dec(v___x_465_);
v___x_467_ = lean_int_mul(v___x_462_, v___x_464_);
lean_dec(v___x_462_);
v_nanos_468_ = lean_int_add(v___x_467_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_467_);
v___x_469_ = lean_int_add(v_nanos_466_, v_nanos_468_);
lean_dec(v_nanos_468_);
lean_dec(v_nanos_466_);
v___x_470_ = l_Std_Time_Duration_ofNanoseconds(v___x_469_);
lean_dec(v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMilliseconds___boxed(lean_object* v_t_471_, lean_object* v_s_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Time_Duration_subMilliseconds(v_t_471_, v_s_472_);
lean_dec(v_s_472_);
lean_dec_ref(v_t_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds(lean_object* v_t_474_, lean_object* v_s_475_){
_start:
{
lean_object* v___x_476_; lean_object* v_second_477_; lean_object* v_nano_478_; lean_object* v_second_479_; lean_object* v_nano_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_nanos_485_; lean_object* v___x_486_; lean_object* v_nanos_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_476_ = l_Std_Time_Duration_ofNanoseconds(v_s_475_);
v_second_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_second_477_);
v_nano_478_ = lean_ctor_get(v___x_476_, 1);
lean_inc(v_nano_478_);
lean_dec_ref(v___x_476_);
v_second_479_ = lean_ctor_get(v_t_474_, 0);
v_nano_480_ = lean_ctor_get(v_t_474_, 1);
v___x_481_ = lean_int_neg(v_second_477_);
lean_dec(v_second_477_);
v___x_482_ = lean_int_neg(v_nano_478_);
lean_dec(v_nano_478_);
v___x_483_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_484_ = lean_int_mul(v_second_479_, v___x_483_);
v_nanos_485_ = lean_int_add(v___x_484_, v_nano_480_);
lean_dec(v___x_484_);
v___x_486_ = lean_int_mul(v___x_481_, v___x_483_);
lean_dec(v___x_481_);
v_nanos_487_ = lean_int_add(v___x_486_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v___x_486_);
v___x_488_ = lean_int_add(v_nanos_485_, v_nanos_487_);
lean_dec(v_nanos_487_);
lean_dec(v_nanos_485_);
v___x_489_ = l_Std_Time_Duration_ofNanoseconds(v___x_488_);
lean_dec(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subNanoseconds___boxed(lean_object* v_t_490_, lean_object* v_s_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Time_Duration_subNanoseconds(v_t_490_, v_s_491_);
lean_dec(v_s_491_);
lean_dec_ref(v_t_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds(lean_object* v_t_493_, lean_object* v_s_494_){
_start:
{
lean_object* v_second_495_; lean_object* v_nano_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_nanos_500_; lean_object* v___x_501_; lean_object* v_nanos_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_second_495_ = lean_ctor_get(v_t_493_, 0);
v_nano_496_ = lean_ctor_get(v_t_493_, 1);
v___x_497_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_498_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_499_ = lean_int_mul(v_second_495_, v___x_498_);
v_nanos_500_ = lean_int_add(v___x_499_, v_nano_496_);
lean_dec(v___x_499_);
v___x_501_ = lean_int_mul(v_s_494_, v___x_498_);
v_nanos_502_ = lean_int_add(v___x_501_, v___x_497_);
lean_dec(v___x_501_);
v___x_503_ = lean_int_add(v_nanos_500_, v_nanos_502_);
lean_dec(v_nanos_502_);
lean_dec(v_nanos_500_);
v___x_504_ = l_Std_Time_Duration_ofNanoseconds(v___x_503_);
lean_dec(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addSeconds___boxed(lean_object* v_t_505_, lean_object* v_s_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Time_Duration_addSeconds(v_t_505_, v_s_506_);
lean_dec(v_s_506_);
lean_dec_ref(v_t_505_);
return v_res_507_;
}
}
static lean_object* _init_l_Std_Time_Duration_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_509_ = lean_int_neg(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds(lean_object* v_t_510_, lean_object* v_s_511_){
_start:
{
lean_object* v_second_512_; lean_object* v_nano_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_nanos_518_; lean_object* v___x_519_; lean_object* v_nanos_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_second_512_ = lean_ctor_get(v_t_510_, 0);
v_nano_513_ = lean_ctor_get(v_t_510_, 1);
v___x_514_ = lean_int_neg(v_s_511_);
v___x_515_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_516_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_517_ = lean_int_mul(v_second_512_, v___x_516_);
v_nanos_518_ = lean_int_add(v___x_517_, v_nano_513_);
lean_dec(v___x_517_);
v___x_519_ = lean_int_mul(v___x_514_, v___x_516_);
lean_dec(v___x_514_);
v_nanos_520_ = lean_int_add(v___x_519_, v___x_515_);
lean_dec(v___x_519_);
v___x_521_ = lean_int_add(v_nanos_518_, v_nanos_520_);
lean_dec(v_nanos_520_);
lean_dec(v_nanos_518_);
v___x_522_ = l_Std_Time_Duration_ofNanoseconds(v___x_521_);
lean_dec(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subSeconds___boxed(lean_object* v_t_523_, lean_object* v_s_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_Duration_subSeconds(v_t_523_, v_s_524_);
lean_dec(v_s_524_);
lean_dec_ref(v_t_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes(lean_object* v_t_526_, lean_object* v_m_527_){
_start:
{
lean_object* v_second_528_; lean_object* v_nano_529_; lean_object* v___x_530_; lean_object* v_seconds_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_nanos_535_; lean_object* v___x_536_; lean_object* v_nanos_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_second_528_ = lean_ctor_get(v_t_526_, 0);
v_nano_529_ = lean_ctor_get(v_t_526_, 1);
v___x_530_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v_seconds_531_ = lean_int_mul(v_m_527_, v___x_530_);
v___x_532_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_533_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_534_ = lean_int_mul(v_second_528_, v___x_533_);
v_nanos_535_ = lean_int_add(v___x_534_, v_nano_529_);
lean_dec(v___x_534_);
v___x_536_ = lean_int_mul(v_seconds_531_, v___x_533_);
lean_dec(v_seconds_531_);
v_nanos_537_ = lean_int_add(v___x_536_, v___x_532_);
lean_dec(v___x_536_);
v___x_538_ = lean_int_add(v_nanos_535_, v_nanos_537_);
lean_dec(v_nanos_537_);
lean_dec(v_nanos_535_);
v___x_539_ = l_Std_Time_Duration_ofNanoseconds(v___x_538_);
lean_dec(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addMinutes___boxed(lean_object* v_t_540_, lean_object* v_m_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Time_Duration_addMinutes(v_t_540_, v_m_541_);
lean_dec(v_m_541_);
lean_dec_ref(v_t_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes(lean_object* v_t_543_, lean_object* v_m_544_){
_start:
{
lean_object* v_second_545_; lean_object* v_nano_546_; lean_object* v___x_547_; lean_object* v_seconds_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_nanos_553_; lean_object* v___x_554_; lean_object* v_nanos_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_second_545_ = lean_ctor_get(v_t_543_, 0);
v_nano_546_ = lean_ctor_get(v_t_543_, 1);
v___x_547_ = lean_obj_once(&l_Std_Time_Duration_toMinutes___closed__0, &l_Std_Time_Duration_toMinutes___closed__0_once, _init_l_Std_Time_Duration_toMinutes___closed__0);
v_seconds_548_ = lean_int_mul(v_m_544_, v___x_547_);
v___x_549_ = lean_int_neg(v_seconds_548_);
lean_dec(v_seconds_548_);
v___x_550_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_551_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_552_ = lean_int_mul(v_second_545_, v___x_551_);
v_nanos_553_ = lean_int_add(v___x_552_, v_nano_546_);
lean_dec(v___x_552_);
v___x_554_ = lean_int_mul(v___x_549_, v___x_551_);
lean_dec(v___x_549_);
v_nanos_555_ = lean_int_add(v___x_554_, v___x_550_);
lean_dec(v___x_554_);
v___x_556_ = lean_int_add(v_nanos_553_, v_nanos_555_);
lean_dec(v_nanos_555_);
lean_dec(v_nanos_553_);
v___x_557_ = l_Std_Time_Duration_ofNanoseconds(v___x_556_);
lean_dec(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subMinutes___boxed(lean_object* v_t_558_, lean_object* v_m_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Time_Duration_subMinutes(v_t_558_, v_m_559_);
lean_dec(v_m_559_);
lean_dec_ref(v_t_558_);
return v_res_560_;
}
}
static lean_object* _init_l_Std_Time_Duration_addHours___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(3600u);
v___x_562_ = lean_nat_to_int(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours(lean_object* v_t_563_, lean_object* v_h_564_){
_start:
{
lean_object* v_second_565_; lean_object* v_nano_566_; lean_object* v___x_567_; lean_object* v_seconds_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_nanos_572_; lean_object* v___x_573_; lean_object* v_nanos_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_second_565_ = lean_ctor_get(v_t_563_, 0);
v_nano_566_ = lean_ctor_get(v_t_563_, 1);
v___x_567_ = lean_obj_once(&l_Std_Time_Duration_addHours___closed__0, &l_Std_Time_Duration_addHours___closed__0_once, _init_l_Std_Time_Duration_addHours___closed__0);
v_seconds_568_ = lean_int_mul(v_h_564_, v___x_567_);
v___x_569_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_570_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_571_ = lean_int_mul(v_second_565_, v___x_570_);
v_nanos_572_ = lean_int_add(v___x_571_, v_nano_566_);
lean_dec(v___x_571_);
v___x_573_ = lean_int_mul(v_seconds_568_, v___x_570_);
lean_dec(v_seconds_568_);
v_nanos_574_ = lean_int_add(v___x_573_, v___x_569_);
lean_dec(v___x_573_);
v___x_575_ = lean_int_add(v_nanos_572_, v_nanos_574_);
lean_dec(v_nanos_574_);
lean_dec(v_nanos_572_);
v___x_576_ = l_Std_Time_Duration_ofNanoseconds(v___x_575_);
lean_dec(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addHours___boxed(lean_object* v_t_577_, lean_object* v_h_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Time_Duration_addHours(v_t_577_, v_h_578_);
lean_dec(v_h_578_);
lean_dec_ref(v_t_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours(lean_object* v_t_580_, lean_object* v_h_581_){
_start:
{
lean_object* v_second_582_; lean_object* v_nano_583_; lean_object* v___x_584_; lean_object* v_seconds_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_nanos_590_; lean_object* v___x_591_; lean_object* v_nanos_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_second_582_ = lean_ctor_get(v_t_580_, 0);
v_nano_583_ = lean_ctor_get(v_t_580_, 1);
v___x_584_ = lean_obj_once(&l_Std_Time_Duration_addHours___closed__0, &l_Std_Time_Duration_addHours___closed__0_once, _init_l_Std_Time_Duration_addHours___closed__0);
v_seconds_585_ = lean_int_mul(v_h_581_, v___x_584_);
v___x_586_ = lean_int_neg(v_seconds_585_);
lean_dec(v_seconds_585_);
v___x_587_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_588_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_589_ = lean_int_mul(v_second_582_, v___x_588_);
v_nanos_590_ = lean_int_add(v___x_589_, v_nano_583_);
lean_dec(v___x_589_);
v___x_591_ = lean_int_mul(v___x_586_, v___x_588_);
lean_dec(v___x_586_);
v_nanos_592_ = lean_int_add(v___x_591_, v___x_587_);
lean_dec(v___x_591_);
v___x_593_ = lean_int_add(v_nanos_590_, v_nanos_592_);
lean_dec(v_nanos_592_);
lean_dec(v_nanos_590_);
v___x_594_ = l_Std_Time_Duration_ofNanoseconds(v___x_593_);
lean_dec(v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subHours___boxed(lean_object* v_t_595_, lean_object* v_h_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Time_Duration_subHours(v_t_595_, v_h_596_);
lean_dec(v_h_596_);
lean_dec_ref(v_t_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays(lean_object* v_t_598_, lean_object* v_d_599_){
_start:
{
lean_object* v_second_600_; lean_object* v_nano_601_; lean_object* v___x_602_; lean_object* v_seconds_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_nanos_607_; lean_object* v___x_608_; lean_object* v_nanos_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_second_600_ = lean_ctor_get(v_t_598_, 0);
v_nano_601_ = lean_ctor_get(v_t_598_, 1);
v___x_602_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v_seconds_603_ = lean_int_mul(v_d_599_, v___x_602_);
v___x_604_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_605_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_606_ = lean_int_mul(v_second_600_, v___x_605_);
v_nanos_607_ = lean_int_add(v___x_606_, v_nano_601_);
lean_dec(v___x_606_);
v___x_608_ = lean_int_mul(v_seconds_603_, v___x_605_);
lean_dec(v_seconds_603_);
v_nanos_609_ = lean_int_add(v___x_608_, v___x_604_);
lean_dec(v___x_608_);
v___x_610_ = lean_int_add(v_nanos_607_, v_nanos_609_);
lean_dec(v_nanos_609_);
lean_dec(v_nanos_607_);
v___x_611_ = l_Std_Time_Duration_ofNanoseconds(v___x_610_);
lean_dec(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addDays___boxed(lean_object* v_t_612_, lean_object* v_d_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Time_Duration_addDays(v_t_612_, v_d_613_);
lean_dec(v_d_613_);
lean_dec_ref(v_t_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays(lean_object* v_t_615_, lean_object* v_d_616_){
_start:
{
lean_object* v_second_617_; lean_object* v_nano_618_; lean_object* v___x_619_; lean_object* v_seconds_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_nanos_625_; lean_object* v___x_626_; lean_object* v_nanos_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_second_617_ = lean_ctor_get(v_t_615_, 0);
v_nano_618_ = lean_ctor_get(v_t_615_, 1);
v___x_619_ = lean_obj_once(&l_Std_Time_Duration_toDays___closed__0, &l_Std_Time_Duration_toDays___closed__0_once, _init_l_Std_Time_Duration_toDays___closed__0);
v_seconds_620_ = lean_int_mul(v_d_616_, v___x_619_);
v___x_621_ = lean_int_neg(v_seconds_620_);
lean_dec(v_seconds_620_);
v___x_622_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_623_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_624_ = lean_int_mul(v_second_617_, v___x_623_);
v_nanos_625_ = lean_int_add(v___x_624_, v_nano_618_);
lean_dec(v___x_624_);
v___x_626_ = lean_int_mul(v___x_621_, v___x_623_);
lean_dec(v___x_621_);
v_nanos_627_ = lean_int_add(v___x_626_, v___x_622_);
lean_dec(v___x_626_);
v___x_628_ = lean_int_add(v_nanos_625_, v_nanos_627_);
lean_dec(v_nanos_627_);
lean_dec(v_nanos_625_);
v___x_629_ = l_Std_Time_Duration_ofNanoseconds(v___x_628_);
lean_dec(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subDays___boxed(lean_object* v_t_630_, lean_object* v_d_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Time_Duration_subDays(v_t_630_, v_d_631_);
lean_dec(v_d_631_);
lean_dec_ref(v_t_630_);
return v_res_632_;
}
}
static lean_object* _init_l_Std_Time_Duration_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(604800u);
v___x_634_ = lean_nat_to_int(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks(lean_object* v_t_635_, lean_object* v_w_636_){
_start:
{
lean_object* v_second_637_; lean_object* v_nano_638_; lean_object* v___x_639_; lean_object* v_seconds_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_nanos_644_; lean_object* v___x_645_; lean_object* v_nanos_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_second_637_ = lean_ctor_get(v_t_635_, 0);
v_nano_638_ = lean_ctor_get(v_t_635_, 1);
v___x_639_ = lean_obj_once(&l_Std_Time_Duration_addWeeks___closed__0, &l_Std_Time_Duration_addWeeks___closed__0_once, _init_l_Std_Time_Duration_addWeeks___closed__0);
v_seconds_640_ = lean_int_mul(v_w_636_, v___x_639_);
v___x_641_ = lean_obj_once(&l_Std_Time_instToStringDuration___lam__0___closed__1, &l_Std_Time_instToStringDuration___lam__0___closed__1_once, _init_l_Std_Time_instToStringDuration___lam__0___closed__1);
v___x_642_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_643_ = lean_int_mul(v_second_637_, v___x_642_);
v_nanos_644_ = lean_int_add(v___x_643_, v_nano_638_);
lean_dec(v___x_643_);
v___x_645_ = lean_int_mul(v_seconds_640_, v___x_642_);
lean_dec(v_seconds_640_);
v_nanos_646_ = lean_int_add(v___x_645_, v___x_641_);
lean_dec(v___x_645_);
v___x_647_ = lean_int_add(v_nanos_644_, v_nanos_646_);
lean_dec(v_nanos_646_);
lean_dec(v_nanos_644_);
v___x_648_ = l_Std_Time_Duration_ofNanoseconds(v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_addWeeks___boxed(lean_object* v_t_649_, lean_object* v_w_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Time_Duration_addWeeks(v_t_649_, v_w_650_);
lean_dec(v_w_650_);
lean_dec_ref(v_t_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks(lean_object* v_t_652_, lean_object* v_w_653_){
_start:
{
lean_object* v_second_654_; lean_object* v_nano_655_; lean_object* v___x_656_; lean_object* v_seconds_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_nanos_662_; lean_object* v___x_663_; lean_object* v_nanos_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_second_654_ = lean_ctor_get(v_t_652_, 0);
v_nano_655_ = lean_ctor_get(v_t_652_, 1);
v___x_656_ = lean_obj_once(&l_Std_Time_Duration_addWeeks___closed__0, &l_Std_Time_Duration_addWeeks___closed__0_once, _init_l_Std_Time_Duration_addWeeks___closed__0);
v_seconds_657_ = lean_int_mul(v_w_653_, v___x_656_);
v___x_658_ = lean_int_neg(v_seconds_657_);
lean_dec(v_seconds_657_);
v___x_659_ = lean_obj_once(&l_Std_Time_Duration_subSeconds___closed__0, &l_Std_Time_Duration_subSeconds___closed__0_once, _init_l_Std_Time_Duration_subSeconds___closed__0);
v___x_660_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_661_ = lean_int_mul(v_second_654_, v___x_660_);
v_nanos_662_ = lean_int_add(v___x_661_, v_nano_655_);
lean_dec(v___x_661_);
v___x_663_ = lean_int_mul(v___x_658_, v___x_660_);
lean_dec(v___x_658_);
v_nanos_664_ = lean_int_add(v___x_663_, v___x_659_);
lean_dec(v___x_663_);
v___x_665_ = lean_int_add(v_nanos_662_, v_nanos_664_);
lean_dec(v_nanos_664_);
lean_dec(v_nanos_662_);
v___x_666_ = l_Std_Time_Duration_ofNanoseconds(v___x_665_);
lean_dec(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_subWeeks___boxed(lean_object* v_t_667_, lean_object* v_w_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Time_Duration_subWeeks(v_t_667_, v_w_668_);
lean_dec(v_w_668_);
lean_dec_ref(v_t_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0(lean_object* v_i_729_, lean_object* v_d_730_){
_start:
{
lean_object* v_second_731_; lean_object* v_nano_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_second_731_ = lean_ctor_get(v_d_730_, 0);
v_nano_732_ = lean_ctor_get(v_d_730_, 1);
v___x_733_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_734_ = lean_int_mul(v_second_731_, v___x_733_);
v___x_735_ = lean_int_add(v___x_734_, v_nano_732_);
lean_dec(v___x_734_);
v___x_736_ = lean_int_mul(v___x_735_, v_i_729_);
lean_dec(v___x_735_);
v___x_737_ = l_Std_Time_Duration_ofNanoseconds(v___x_736_);
lean_dec(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt___lam__0___boxed(lean_object* v_i_738_, lean_object* v_d_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_Time_Duration_instHMulInt___lam__0(v_i_738_, v_d_739_);
lean_dec_ref(v_d_739_);
lean_dec(v_i_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0(lean_object* v_d_743_, lean_object* v_i_744_){
_start:
{
lean_object* v_second_745_; lean_object* v_nano_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_second_745_ = lean_ctor_get(v_d_743_, 0);
v_nano_746_ = lean_ctor_get(v_d_743_, 1);
v___x_747_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_748_ = lean_int_mul(v_second_745_, v___x_747_);
v___x_749_ = lean_int_add(v___x_748_, v_nano_746_);
lean_dec(v___x_748_);
v___x_750_ = lean_int_mul(v___x_749_, v_i_744_);
lean_dec(v___x_749_);
v___x_751_ = l_Std_Time_Duration_ofNanoseconds(v___x_750_);
lean_dec(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHMulInt__1___lam__0___boxed(lean_object* v_d_752_, lean_object* v_i_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_Time_Duration_instHMulInt__1___lam__0(v_d_752_, v_i_753_);
lean_dec(v_i_753_);
lean_dec_ref(v_d_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0(lean_object* v_pt_757_, lean_object* v_d_758_){
_start:
{
lean_object* v_second_759_; lean_object* v_nano_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_nanos_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_second_759_ = lean_ctor_get(v_d_758_, 0);
v_nano_760_ = lean_ctor_get(v_d_758_, 1);
v___x_761_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_762_ = lean_int_mul(v_second_759_, v___x_761_);
v_nanos_763_ = lean_int_add(v___x_762_, v_nano_760_);
lean_dec(v___x_762_);
v___x_764_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_757_);
v___x_765_ = lean_int_add(v_nanos_763_, v___x_764_);
lean_dec(v___x_764_);
lean_dec(v_nanos_763_);
v___x_766_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_765_);
lean_dec(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed(lean_object* v_pt_767_, lean_object* v_d_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Time_Duration_instHAddPlainTime___lam__0(v_pt_767_, v_d_768_);
lean_dec_ref(v_d_768_);
lean_dec_ref(v_pt_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0(lean_object* v_pt_772_, lean_object* v_d_773_){
_start:
{
lean_object* v_second_774_; lean_object* v_nano_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_nanos_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_second_774_ = lean_ctor_get(v_d_773_, 0);
v_nano_775_ = lean_ctor_get(v_d_773_, 1);
v___x_776_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_772_);
v___x_777_ = lean_obj_once(&l_Std_Time_Duration_ofNanoseconds___closed__0, &l_Std_Time_Duration_ofNanoseconds___closed__0_once, _init_l_Std_Time_Duration_ofNanoseconds___closed__0);
v___x_778_ = lean_int_mul(v_second_774_, v___x_777_);
v_nanos_779_ = lean_int_add(v___x_778_, v_nano_775_);
lean_dec(v___x_778_);
v___x_780_ = lean_int_sub(v___x_776_, v_nanos_779_);
lean_dec(v_nanos_779_);
lean_dec(v___x_776_);
v___x_781_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_780_);
lean_dec(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed(lean_object* v_pt_782_, lean_object* v_d_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Time_Duration_instHSubPlainTime___lam__0(v_pt_782_, v_d_783_);
lean_dec_ref(v_d_783_);
lean_dec_ref(v_pt_782_);
return v_res_784_;
}
}
lean_object* runtime_initialize_Std_Time_Date(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedDuration = _init_l_Std_Time_instInhabitedDuration();
lean_mark_persistent(l_Std_Time_instInhabitedDuration);
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
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
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
res = initialize_Init_Data_String_Length(builtin);
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
