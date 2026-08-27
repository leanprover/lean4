// Lean compiler output
// Module: Std.Time.Zoned.RecurringRule
// Imports: public import Std.Time.Date.Unit.Month public import Std.Time.Date.Unit.Week public import Std.Time.Date.Unit.Weekday public import Std.Time.Zoned.TimeZone public import Std.Time.Date
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_Week_instReprOffset___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_Weekday_instReprOrdinal___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object*);
lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_mwd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_mwd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Time.TimeZone.TransitionSpec.mwd"};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__2_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Std.Time.TimeZone.TransitionSpec.julian"};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__7 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__7_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Time.TimeZone.TransitionSpec.julian0"};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__9_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__9_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__10 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__10_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprTransitionSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprTransitionSpec_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprTransitionSpec = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionSpec___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__1(lean_object*);
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7;
static lean_once_cell_t l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDay(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "time"};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__12_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprTransitionRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprTransitionRule_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprTransitionRule___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprTransitionRule = (const lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule___closed__0_value;
static const lean_string_object l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__5_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6;
static const lean_string_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__7 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9;
static const lean_string_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "end_"};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprDaylightSavingRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule = (const lean_object*)&l_Std_Time_TimeZone_instReprDaylightSavingRule___closed__0_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "stdName"};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "stdOffset"};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__5_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6;
static const lean_string_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dst"};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__7 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprRecurringRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprRecurringRule_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprRecurringRule___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprRecurringRule = (const lean_object*)&l_Std_Time_TimeZone_instReprRecurringRule___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Time_TimeZone_TransitionSpec_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
lean_object* v_month_9_; lean_object* v_week_10_; lean_object* v_day_11_; lean_object* v___x_12_; 
v_month_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_month_9_);
v_week_10_ = lean_ctor_get(v_t_7_, 1);
lean_inc(v_week_10_);
v_day_11_ = lean_ctor_get(v_t_7_, 2);
lean_inc(v_day_11_);
lean_dec_ref_known(v_t_7_, 3);
v___x_12_ = lean_apply_3(v_k_8_, v_month_9_, v_week_10_, v_day_11_);
return v___x_12_;
}
else
{
lean_object* v_day_13_; lean_object* v___x_14_; 
v_day_13_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_day_13_);
lean_dec_ref(v_t_7_);
v___x_14_ = lean_apply_1(v_k_8_, v_day_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_mwd_elim___redArg(lean_object* v_t_27_, lean_object* v_mwd_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_27_, v_mwd_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_mwd_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_mwd_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_31_, v_mwd_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian_elim___redArg(lean_object* v_t_35_, lean_object* v_julian_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_35_, v_julian_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_julian_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_39_, v_julian_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian0_elim___redArg(lean_object* v_t_43_, lean_object* v_julian0_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_43_, v_julian0_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian0_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_julian0_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_47_, v_julian0_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(2u);
v___x_58_ = lean_nat_to_int(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr(lean_object* v_x_75_, lean_object* v_prec_76_){
_start:
{
lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; 
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
lean_object* v_month_95_; lean_object* v_week_96_; lean_object* v_day_97_; lean_object* v___y_99_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_month_95_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_month_95_);
v_week_96_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_week_96_);
v_day_97_ = lean_ctor_get(v_x_75_, 2);
lean_inc(v_day_97_);
lean_dec_ref_known(v_x_75_, 3);
v___x_115_ = lean_unsigned_to_nat(1024u);
v___x_116_ = lean_nat_dec_le(v___x_115_, v_prec_76_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3);
v___y_99_ = v___x_117_;
goto v___jp_98_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_99_ = v___x_118_;
goto v___jp_98_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_100_ = lean_box(1);
v___x_101_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__2));
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = l_Std_Time_Month_instReprOrdinal___lam__0(v_month_95_, v___x_102_);
lean_dec(v_month_95_);
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_100_);
v___x_106_ = l_Std_Time_Week_instReprOffset___lam__0(v_week_96_, v___x_102_);
lean_dec(v_week_96_);
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_100_);
v___x_109_ = l_Std_Time_Weekday_instReprOrdinal___lam__0(v_day_97_, v___x_102_);
lean_dec(v_day_97_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
lean_inc(v___y_99_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_99_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_76_);
return v___x_114_;
}
}
case 1:
{
lean_object* v_day_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_142_; 
v_day_119_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_142_ == 0)
{
v___x_121_ = v_x_75_;
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_day_119_);
lean_dec(v_x_75_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___y_124_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1024u);
v___x_139_ = lean_nat_dec_le(v___x_138_, v_prec_76_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3);
v___y_124_ = v___x_140_;
goto v___jp_123_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_124_ = v___x_141_;
goto v___jp_123_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__7));
v___x_126_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_127_ = lean_int_dec_lt(v_day_119_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = l_Int_repr(v_day_119_);
lean_dec(v_day_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 3);
lean_ctor_set(v___x_121_, 0, v___x_128_);
v___x_130_ = v___x_121_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
v___y_87_ = v___y_124_;
v___y_88_ = v___x_125_;
v___y_89_ = v___x_130_;
goto v___jp_86_;
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = l_Int_repr(v_day_119_);
lean_dec(v_day_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 3);
lean_ctor_set(v___x_121_, 0, v___x_133_);
v___x_135_ = v___x_121_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_137_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; 
v___x_136_ = l_Repr_addAppParen(v___x_135_, v___x_132_);
v___y_87_ = v___y_124_;
v___y_88_ = v___x_125_;
v___y_89_ = v___x_136_;
goto v___jp_86_;
}
}
}
}
}
default: 
{
lean_object* v_day_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_166_; 
v_day_143_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_166_ == 0)
{
v___x_145_ = v_x_75_;
v_isShared_146_ = v_isSharedCheck_166_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_day_143_);
lean_dec(v_x_75_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_166_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___y_148_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1024u);
v___x_163_ = lean_nat_dec_le(v___x_162_, v_prec_76_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3);
v___y_148_ = v___x_164_;
goto v___jp_147_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_148_ = v___x_165_;
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__11));
v___x_150_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_151_ = lean_int_dec_lt(v_day_143_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = l_Int_repr(v_day_143_);
lean_dec(v_day_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 3);
lean_ctor_set(v___x_145_, 0, v___x_152_);
v___x_154_ = v___x_145_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
v___y_78_ = v___y_148_;
v___y_79_ = v___x_149_;
v___y_80_ = v___x_154_;
goto v___jp_77_;
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_156_ = lean_unsigned_to_nat(1024u);
v___x_157_ = l_Int_repr(v_day_143_);
lean_dec(v_day_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 3);
lean_ctor_set(v___x_145_, 0, v___x_157_);
v___x_159_ = v___x_145_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_161_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; 
v___x_160_ = l_Repr_addAppParen(v___x_159_, v___x_156_);
v___y_78_ = v___y_148_;
v___y_79_ = v___x_149_;
v___y_80_ = v___x_160_;
goto v___jp_77_;
}
}
}
}
}
}
v___jp_77_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_inc(v___y_79_);
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___y_79_);
lean_ctor_set(v___x_81_, 1, v___y_80_);
lean_inc(v___y_78_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_78_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_76_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_inc(v___y_88_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___y_88_);
lean_ctor_set(v___x_90_, 1, v___y_89_);
lean_inc(v___y_87_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_76_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___boxed(lean_object* v_x_167_, lean_object* v_prec_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Time_TimeZone_instReprTransitionSpec_repr(v_x_167_, v_prec_168_);
lean_dec(v_prec_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__1(lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_nat_to_int(v_a_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(7u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(5u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_179_ = lean_int_neg(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(30u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_183_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_184_ = lean_int_add(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_186_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_187_ = lean_int_sub(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_range_190_; 
v___x_188_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_189_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5);
v_range_190_ = lean_int_add(v___x_189_, v___x_188_);
return v_range_190_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_192_ = lean_int_sub(v___x_191_, v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8(void){
_start:
{
lean_object* v_range_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_range_193_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6);
v___x_194_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7);
v___x_195_ = lean_int_emod(v___x_194_, v_range_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9(void){
_start:
{
lean_object* v_range_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_range_196_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6);
v___x_197_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8);
v___x_198_ = lean_int_add(v___x_197_, v_range_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10(void){
_start:
{
lean_object* v_range_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_range_199_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6);
v___x_200_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_201_ = lean_int_emod(v___x_200_, v_range_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_203_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10);
v___x_204_ = lean_int_add(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(4u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(100u);
v___x_208_ = lean_nat_to_int(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(400u);
v___x_210_ = lean_nat_to_int(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(lean_object* v_year_211_, lean_object* v_month_212_, lean_object* v_week_213_, lean_object* v_day_214_){
_start:
{
uint8_t v___y_216_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_228_ = lean_int_dec_eq(v_week_213_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___y_230_; lean_object* v___x_243_; uint8_t v___y_245_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; uint8_t v___y_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_243_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11);
v___x_250_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_251_ = lean_int_mod(v_year_211_, v___x_250_);
v___x_252_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_253_ = lean_int_dec_eq(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
v___x_256_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_257_ = lean_int_mod(v_year_211_, v___x_256_);
v___x_258_ = lean_int_dec_eq(v___x_257_, v___x_252_);
lean_dec(v___x_257_);
if (v___x_258_ == 0)
{
uint8_t v___x_259_; 
v___x_259_ = 1;
v___y_255_ = v___x_259_;
goto v___jp_254_;
}
else
{
if (v___x_228_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_261_ = lean_int_mod(v_year_211_, v___x_260_);
v___x_262_ = lean_int_dec_eq(v___x_261_, v___x_252_);
lean_dec(v___x_261_);
v___y_255_ = v___x_262_;
goto v___jp_254_;
}
else
{
v___y_255_ = v___x_228_;
goto v___jp_254_;
}
}
v___jp_229_:
{
uint8_t v___x_231_; lean_object* v_firstWday_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc_ref(v___y_230_);
v___x_231_ = l_Std_Time_PlainDate_weekday(v___y_230_);
v_firstWday_232_ = l_Std_Time_Weekday_toOrdinal(v___x_231_);
v___x_233_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_234_ = lean_int_neg(v_firstWday_232_);
lean_dec(v_firstWday_232_);
v___x_235_ = lean_int_add(v_day_214_, v___x_234_);
lean_dec(v___x_234_);
v___x_236_ = lean_int_emod(v___x_235_, v___x_233_);
lean_dec(v___x_235_);
v___x_237_ = l_Std_Time_PlainDate_toEpochDay(v___y_230_);
v___x_238_ = lean_int_add(v___x_237_, v___x_236_);
lean_dec(v___x_236_);
lean_dec(v___x_237_);
v___x_239_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_240_ = lean_int_add(v_week_213_, v___x_239_);
v___x_241_ = lean_int_mul(v___x_240_, v___x_233_);
lean_dec(v___x_240_);
v___x_242_ = lean_int_add(v___x_238_, v___x_241_);
lean_dec(v___x_241_);
lean_dec(v___x_238_);
return v___x_242_;
}
v___jp_244_:
{
lean_object* v_max_246_; uint8_t v___x_247_; 
v_max_246_ = l_Std_Time_Month_Ordinal_days(v___y_245_, v_month_212_);
v___x_247_ = lean_int_dec_lt(v_max_246_, v___x_243_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_max_246_);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v_year_211_);
lean_ctor_set(v___x_248_, 1, v_month_212_);
lean_ctor_set(v___x_248_, 2, v___x_243_);
v___y_230_ = v___x_248_;
goto v___jp_229_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_249_, 0, v_year_211_);
lean_ctor_set(v___x_249_, 1, v_month_212_);
lean_ctor_set(v___x_249_, 2, v_max_246_);
v___y_230_ = v___x_249_;
goto v___jp_229_;
}
}
v___jp_254_:
{
if (v___x_253_ == 0)
{
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
else
{
v___y_245_ = v___y_255_;
goto v___jp_244_;
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; uint8_t v___y_268_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_263_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_264_ = lean_int_mod(v_year_211_, v___x_263_);
v___x_265_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_266_ = lean_int_dec_eq(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
v___x_273_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_274_ = lean_int_mod(v_year_211_, v___x_273_);
v___x_275_ = lean_int_dec_eq(v___x_274_, v___x_265_);
lean_dec(v___x_274_);
if (v___x_275_ == 0)
{
if (v___x_228_ == 0)
{
goto v___jp_269_;
}
else
{
v___y_268_ = v___x_228_;
goto v___jp_267_;
}
}
else
{
goto v___jp_269_;
}
v___jp_267_:
{
if (v___x_266_ == 0)
{
v___y_216_ = v___x_266_;
goto v___jp_215_;
}
else
{
v___y_216_ = v___y_268_;
goto v___jp_215_;
}
}
v___jp_269_:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_271_ = lean_int_mod(v_year_211_, v___x_270_);
v___x_272_ = lean_int_dec_eq(v___x_271_, v___x_265_);
lean_dec(v___x_271_);
v___y_268_ = v___x_272_;
goto v___jp_267_;
}
}
v___jp_215_:
{
lean_object* v_lastDay_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v_lastWday_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_lastDay_217_ = l_Std_Time_Month_Ordinal_days(v___y_216_, v_month_212_);
v___x_218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_218_, 0, v_year_211_);
lean_ctor_set(v___x_218_, 1, v_month_212_);
lean_ctor_set(v___x_218_, 2, v_lastDay_217_);
lean_inc_ref(v___x_218_);
v___x_219_ = l_Std_Time_PlainDate_weekday(v___x_218_);
v_lastWday_220_ = l_Std_Time_Weekday_toOrdinal(v___x_219_);
v___x_221_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_222_ = lean_int_neg(v_day_214_);
v___x_223_ = lean_int_add(v_lastWday_220_, v___x_222_);
lean_dec(v___x_222_);
lean_dec(v_lastWday_220_);
v___x_224_ = lean_int_emod(v___x_223_, v___x_221_);
lean_dec(v___x_223_);
v___x_225_ = l_Std_Time_PlainDate_toEpochDay(v___x_218_);
v___x_226_ = lean_int_sub(v___x_225_, v___x_224_);
lean_dec(v___x_224_);
lean_dec(v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___boxed(lean_object* v_year_276_, lean_object* v_month_277_, lean_object* v_week_278_, lean_object* v_day_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(v_year_276_, v_month_277_, v_week_278_, v_day_279_);
lean_dec(v_day_279_);
lean_dec(v_week_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__0(lean_object* v_a_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_nat_to_int(v_a_281_);
v___x_283_ = l_Rat_ofInt(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(60u);
v___x_285_ = lean_nat_to_int(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(11u);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1);
v___x_289_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_290_ = lean_int_add(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_292_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2);
v___x_293_ = lean_int_sub(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_range_296_; 
v___x_294_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_295_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3);
v_range_296_ = lean_int_add(v___x_295_, v___x_294_);
return v_range_296_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5(void){
_start:
{
lean_object* v_range_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_range_297_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_298_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7);
v___x_299_ = lean_int_emod(v___x_298_, v_range_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6(void){
_start:
{
lean_object* v_range_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_range_300_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_301_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5);
v___x_302_ = lean_int_add(v___x_301_, v_range_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7(void){
_start:
{
lean_object* v_range_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_range_303_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_304_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6);
v___x_305_ = lean_int_emod(v___x_304_, v_range_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_307_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7);
v___x_308_ = lean_int_add(v___x_307_, v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(lean_object* v_year_309_, lean_object* v_day_310_){
_start:
{
lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_320_; uint8_t v___y_323_; lean_object* v___y_324_; uint8_t v___y_325_; lean_object* v___y_330_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___y_345_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; uint8_t v___y_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_342_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8);
v___x_343_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11);
v___x_350_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_351_ = lean_int_mod(v_year_309_, v___x_350_);
v___x_352_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_353_ = lean_int_dec_eq(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
v___x_356_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_357_ = lean_int_mod(v_year_309_, v___x_356_);
v___x_358_ = lean_int_dec_eq(v___x_357_, v___x_352_);
lean_dec(v___x_357_);
if (v___x_358_ == 0)
{
uint8_t v___x_359_; 
v___x_359_ = 1;
v___y_355_ = v___x_359_;
goto v___jp_354_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_361_ = lean_int_mod(v_year_309_, v___x_360_);
v___x_362_ = lean_int_dec_eq(v___x_361_, v___x_352_);
lean_dec(v___x_361_);
v___y_355_ = v___x_362_;
goto v___jp_354_;
}
v___jp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = l_Std_Time_PlainDate_toEpochDay(v___y_312_);
v___x_315_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_316_ = lean_int_sub(v_day_310_, v___x_315_);
v___x_317_ = lean_int_add(v___x_316_, v___y_313_);
lean_dec(v___x_316_);
v___x_318_ = lean_int_add(v___x_314_, v___x_317_);
lean_dec(v___x_317_);
lean_dec(v___x_314_);
return v___x_318_;
}
v___jp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___y_312_ = v___y_320_;
v___y_313_ = v___x_321_;
goto v___jp_311_;
}
v___jp_322_:
{
if (v___y_323_ == 0)
{
v___y_320_ = v___y_324_;
goto v___jp_319_;
}
else
{
if (v___y_325_ == 0)
{
v___y_320_ = v___y_324_;
goto v___jp_319_;
}
else
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0);
v___x_327_ = lean_int_dec_le(v___x_326_, v_day_310_);
if (v___x_327_ == 0)
{
v___y_320_ = v___y_324_;
goto v___jp_319_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_312_ = v___y_324_;
v___y_313_ = v___x_328_;
goto v___jp_311_;
}
}
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_331_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_332_ = lean_int_mod(v_year_309_, v___x_331_);
v___x_333_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_334_ = lean_int_dec_eq(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_336_ = lean_int_mod(v_year_309_, v___x_335_);
v___x_337_ = lean_int_dec_eq(v___x_336_, v___x_333_);
lean_dec(v___x_336_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
lean_dec(v_year_309_);
v___x_338_ = 1;
v___y_323_ = v___x_334_;
v___y_324_ = v___y_330_;
v___y_325_ = v___x_338_;
goto v___jp_322_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_340_ = lean_int_mod(v_year_309_, v___x_339_);
lean_dec(v_year_309_);
v___x_341_ = lean_int_dec_eq(v___x_340_, v___x_333_);
lean_dec(v___x_340_);
v___y_323_ = v___x_334_;
v___y_324_ = v___y_330_;
v___y_325_ = v___x_341_;
goto v___jp_322_;
}
}
v___jp_344_:
{
lean_object* v_max_346_; uint8_t v___x_347_; 
v_max_346_ = l_Std_Time_Month_Ordinal_days(v___y_345_, v___x_342_);
v___x_347_ = lean_int_dec_lt(v_max_346_, v___x_343_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec(v_max_346_);
lean_inc(v_year_309_);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v_year_309_);
lean_ctor_set(v___x_348_, 1, v___x_342_);
lean_ctor_set(v___x_348_, 2, v___x_343_);
v___y_330_ = v___x_348_;
goto v___jp_329_;
}
else
{
lean_object* v___x_349_; 
lean_inc(v_year_309_);
v___x_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_349_, 0, v_year_309_);
lean_ctor_set(v___x_349_, 1, v___x_342_);
lean_ctor_set(v___x_349_, 2, v_max_346_);
v___y_330_ = v___x_349_;
goto v___jp_329_;
}
}
v___jp_354_:
{
if (v___x_353_ == 0)
{
v___y_345_ = v___x_353_;
goto v___jp_344_;
}
else
{
v___y_345_ = v___y_355_;
goto v___jp_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___boxed(lean_object* v_year_363_, lean_object* v_day_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(v_year_363_, v_day_364_);
lean_dec(v_day_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(lean_object* v_year_366_, lean_object* v_day_367_){
_start:
{
lean_object* v___y_369_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___y_375_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; uint8_t v___y_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_372_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8);
v___x_373_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11);
v___x_380_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_381_ = lean_int_mod(v_year_366_, v___x_380_);
v___x_382_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_383_ = lean_int_dec_eq(v___x_381_, v___x_382_);
lean_dec(v___x_381_);
v___x_386_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_387_ = lean_int_mod(v_year_366_, v___x_386_);
v___x_388_ = lean_int_dec_eq(v___x_387_, v___x_382_);
lean_dec(v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = 1;
v___y_385_ = v___x_389_;
goto v___jp_384_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_391_ = lean_int_mod(v_year_366_, v___x_390_);
v___x_392_ = lean_int_dec_eq(v___x_391_, v___x_382_);
lean_dec(v___x_391_);
v___y_385_ = v___x_392_;
goto v___jp_384_;
}
v___jp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = l_Std_Time_PlainDate_toEpochDay(v___y_369_);
v___x_371_ = lean_int_add(v___x_370_, v_day_367_);
lean_dec(v___x_370_);
return v___x_371_;
}
v___jp_374_:
{
lean_object* v_max_376_; uint8_t v___x_377_; 
v_max_376_ = l_Std_Time_Month_Ordinal_days(v___y_375_, v___x_372_);
v___x_377_ = lean_int_dec_lt(v_max_376_, v___x_373_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_max_376_);
v___x_378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_378_, 0, v_year_366_);
lean_ctor_set(v___x_378_, 1, v___x_372_);
lean_ctor_set(v___x_378_, 2, v___x_373_);
v___y_369_ = v___x_378_;
goto v___jp_368_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_379_, 0, v_year_366_);
lean_ctor_set(v___x_379_, 1, v___x_372_);
lean_ctor_set(v___x_379_, 2, v_max_376_);
v___y_369_ = v___x_379_;
goto v___jp_368_;
}
}
v___jp_384_:
{
if (v___x_383_ == 0)
{
v___y_375_ = v___x_383_;
goto v___jp_374_;
}
else
{
v___y_375_ = v___y_385_;
goto v___jp_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0___boxed(lean_object* v_year_393_, lean_object* v_day_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(v_year_393_, v_day_394_);
lean_dec(v_day_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDay(lean_object* v_spec_396_, lean_object* v_year_397_){
_start:
{
switch(lean_obj_tag(v_spec_396_))
{
case 0:
{
lean_object* v_month_398_; lean_object* v_week_399_; lean_object* v_day_400_; lean_object* v___x_401_; 
v_month_398_ = lean_ctor_get(v_spec_396_, 0);
lean_inc(v_month_398_);
v_week_399_ = lean_ctor_get(v_spec_396_, 1);
lean_inc(v_week_399_);
v_day_400_ = lean_ctor_get(v_spec_396_, 2);
lean_inc(v_day_400_);
lean_dec_ref_known(v_spec_396_, 3);
v___x_401_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(v_year_397_, v_month_398_, v_week_399_, v_day_400_);
lean_dec(v_day_400_);
lean_dec(v_week_399_);
return v___x_401_;
}
case 1:
{
lean_object* v_day_402_; lean_object* v___x_403_; 
v_day_402_ = lean_ctor_get(v_spec_396_, 0);
lean_inc(v_day_402_);
lean_dec_ref_known(v_spec_396_, 1);
v___x_403_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(v_year_397_, v_day_402_);
lean_dec(v_day_402_);
return v___x_403_;
}
default: 
{
lean_object* v_day_404_; lean_object* v___x_405_; 
v_day_404_ = lean_ctor_get(v_spec_396_, 0);
lean_inc(v_day_404_);
lean_dec_ref_known(v_spec_396_, 1);
v___x_405_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(v_year_397_, v_day_404_);
lean_dec(v_day_404_);
return v___x_405_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(8u);
v___x_420_ = lean_nat_to_int(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0));
v___x_429_ = lean_string_length(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13);
v___x_431_ = lean_nat_to_int(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(lean_object* v_x_436_){
_start:
{
lean_object* v_spec_437_; lean_object* v_time_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_471_; 
v_spec_437_ = lean_ctor_get(v_x_436_, 0);
v_time_438_ = lean_ctor_get(v_x_436_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_471_ == 0)
{
v___x_440_ = v_x_436_;
v_isShared_441_ = v_isSharedCheck_471_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_time_438_);
lean_inc(v_spec_437_);
lean_dec(v_x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_471_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_442_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_443_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__6));
v___x_444_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = l_Std_Time_TimeZone_instReprTransitionSpec_repr(v_spec_437_, v___x_445_);
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 4);
lean_ctor_set(v___x_440_, 1, v___x_446_);
lean_ctor_set(v___x_440_, 0, v___x_444_);
v___x_448_ = v___x_440_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_470_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_449_ = 0;
v___x_450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_449_);
v___x_451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_443_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_box(1);
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__11));
v___x_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_442_);
v___x_459_ = l_Std_Time_Second_instReprOffset___lam__0(v_time_438_, v___x_445_);
lean_dec(v_time_438_);
v___x_460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_444_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*1, v___x_449_);
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_458_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_464_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_462_);
v___x_466_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_463_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*1, v___x_449_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr(lean_object* v_x_472_, lean_object* v_prec_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(v_x_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___boxed(lean_object* v_x_475_, lean_object* v_prec_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Time_TimeZone_instReprTransitionRule_repr(v_x_475_, v_prec_476_);
lean_dec(v_prec_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1));
return v___x_488_;
}
else
{
lean_object* v_val_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_val_489_ = lean_ctor_get(v_x_486_, 0);
lean_inc(v_val_489_);
lean_dec_ref_known(v_x_486_, 1);
v___x_490_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3));
v___x_491_ = l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(v_val_489_);
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Repr_addAppParen(v___x_492_, v_x_487_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___boxed(lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_x_494_, v_x_495_);
lean_dec(v_x_495_);
return v_res_496_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(10u);
v___x_510_ = lean_nat_to_int(v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(9u);
v___x_515_ = lean_nat_to_int(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(lean_object* v_x_519_){
_start:
{
lean_object* v_name_520_; lean_object* v_offset_521_; lean_object* v_start_522_; lean_object* v_end___523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_name_520_ = lean_ctor_get(v_x_519_, 0);
lean_inc_ref(v_name_520_);
v_offset_521_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_offset_521_);
v_start_522_ = lean_ctor_get(v_x_519_, 2);
lean_inc(v_start_522_);
v_end___523_ = lean_ctor_get(v_x_519_, 3);
lean_inc(v_end___523_);
lean_dec_ref(v_x_519_);
v___x_524_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_525_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__3));
v___x_526_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7);
v___x_527_ = l_String_quote(v_name_520_);
v___x_528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_526_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = 0;
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_525_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_box(1);
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__5));
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_524_);
v___x_540_ = lean_obj_once(&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_521_);
lean_dec(v_offset_521_);
v___x_543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_540_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*1, v___x_530_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_539_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_533_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_535_);
v___x_548_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__8));
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_524_);
v___x_551_ = lean_obj_once(&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9, &l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9_once, _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9);
v___x_552_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_start_522_, v___x_541_);
v___x_553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*1, v___x_530_);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_550_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_533_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_535_);
v___x_558_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__11));
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_524_);
v___x_561_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_end___523_, v___x_541_);
v___x_562_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_526_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*1, v___x_530_);
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_560_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_566_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_564_);
v___x_568_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_565_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*1, v___x_530_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(lean_object* v_x_572_, lean_object* v_prec_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(v_x_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___boxed(lean_object* v_x_575_, lean_object* v_prec_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(v_x_575_, v_prec_576_);
lean_dec(v_prec_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1));
return v___x_582_;
}
else
{
lean_object* v_val_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_val_583_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_x_580_, 1);
v___x_584_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3));
v___x_585_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(v_val_583_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Repr_addAppParen(v___x_586_, v_x_581_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0___boxed(lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(v_x_588_, v_x_589_);
lean_dec(v_x_589_);
return v_res_590_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(13u);
v___x_604_ = lean_nat_to_int(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(lean_object* v_x_608_){
_start:
{
lean_object* v_stdName_609_; lean_object* v_stdOffset_610_; lean_object* v_dst_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_stdName_609_ = lean_ctor_get(v_x_608_, 0);
lean_inc_ref(v_stdName_609_);
v_stdOffset_610_ = lean_ctor_get(v_x_608_, 1);
lean_inc(v_stdOffset_610_);
v_dst_611_ = lean_ctor_get(v_x_608_, 2);
lean_inc(v_dst_611_);
lean_dec_ref(v_x_608_);
v___x_612_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_613_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__3));
v___x_614_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1);
v___x_615_ = l_String_quote(v_stdName_609_);
v___x_616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
v___x_617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_614_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = 0;
v___x_619_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*1, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_613_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_box(1);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__5));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_612_);
v___x_628_ = lean_obj_once(&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_stdOffset_610_);
lean_dec(v_stdOffset_610_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_618_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_627_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_621_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_623_);
v___x_636_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__8));
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_612_);
v___x_639_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_640_ = l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(v_dst_611_, v___x_629_);
v___x_641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*1, v___x_618_);
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_638_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_645_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_643_);
v___x_647_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_644_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v___x_618_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr(lean_object* v_x_651_, lean_object* v_prec_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_x_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___boxed(lean_object* v_x_654_, lean_object* v_prec_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_Time_TimeZone_instReprRecurringRule_repr(v_x_654_, v_prec_655_);
lean_dec(v_prec_655_);
return v_res_656_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Week(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Week(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Week(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* initialize_Std_Time_Date(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Week(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_RecurringRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_RecurringRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_RecurringRule(builtin);
}
#ifdef __cplusplus
}
#endif
