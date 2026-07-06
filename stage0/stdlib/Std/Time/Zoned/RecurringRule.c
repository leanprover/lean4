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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object*);
lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
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
v___y_87_ = v___x_125_;
v___y_88_ = v___y_124_;
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
v___y_87_ = v___x_125_;
v___y_88_ = v___y_124_;
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
lean_inc(v___y_87_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___y_87_);
lean_ctor_set(v___x_90_, 1, v___y_89_);
lean_inc(v___y_88_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_88_);
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
v___x_178_ = lean_unsigned_to_nat(400u);
v___x_179_ = lean_nat_to_int(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(4u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(100u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_185_ = lean_int_neg(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(30u);
v___x_187_ = lean_nat_to_int(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6);
v___x_189_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_190_ = lean_int_add(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_192_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7);
v___x_193_ = lean_int_sub(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_range_196_; 
v___x_194_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_195_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8);
v_range_196_ = lean_int_add(v___x_195_, v___x_194_);
return v_range_196_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_198_ = lean_int_sub(v___x_197_, v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11(void){
_start:
{
lean_object* v_range_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_range_199_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_200_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10);
v___x_201_ = lean_int_emod(v___x_200_, v_range_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12(void){
_start:
{
lean_object* v_range_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_range_202_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_203_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11);
v___x_204_ = lean_int_add(v___x_203_, v_range_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13(void){
_start:
{
lean_object* v_range_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_range_205_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_206_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_207_ = lean_int_emod(v___x_206_, v_range_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_209_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_210_ = lean_int_add(v___x_209_, v___x_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(lean_object* v_year_211_, lean_object* v_month_212_, lean_object* v_week_213_, lean_object* v_day_214_){
_start:
{
lean_object* v___y_216_; lean_object* v___y_226_; uint8_t v___y_227_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___y_235_; lean_object* v___y_236_; uint8_t v___y_241_; 
v___x_232_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_233_ = lean_int_dec_eq(v_week_213_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___y_251_; lean_object* v___x_264_; uint8_t v___y_266_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___y_275_; uint8_t v___x_279_; 
v___x_264_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_271_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_272_ = lean_int_mod(v_year_211_, v___x_271_);
v___x_273_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_279_ = lean_int_dec_eq(v___x_272_, v___x_273_);
lean_dec(v___x_272_);
if (v___x_279_ == 0)
{
v___y_266_ = v___x_233_;
goto v___jp_265_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_281_ = lean_int_mod(v_year_211_, v___x_280_);
v___x_282_ = lean_int_dec_eq(v___x_281_, v___x_273_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
v___y_275_ = v___x_279_;
goto v___jp_274_;
}
else
{
v___y_275_ = v___x_233_;
goto v___jp_274_;
}
}
v___jp_250_:
{
uint8_t v___x_252_; lean_object* v_firstWday_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc_ref(v___y_251_);
v___x_252_ = l_Std_Time_PlainDate_weekday(v___y_251_);
v_firstWday_253_ = l_Std_Time_Weekday_toOrdinal(v___x_252_);
v___x_254_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_255_ = lean_int_neg(v_firstWday_253_);
lean_dec(v_firstWday_253_);
v___x_256_ = lean_int_add(v_day_214_, v___x_255_);
lean_dec(v___x_255_);
v___x_257_ = lean_int_emod(v___x_256_, v___x_254_);
lean_dec(v___x_256_);
v___x_258_ = l_Std_Time_PlainDate_toEpochDay(v___y_251_);
v___x_259_ = lean_int_add(v___x_258_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v___x_258_);
v___x_260_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5);
v___x_261_ = lean_int_add(v_week_213_, v___x_260_);
v___x_262_ = lean_int_mul(v___x_261_, v___x_254_);
lean_dec(v___x_261_);
v___x_263_ = lean_int_add(v___x_259_, v___x_262_);
lean_dec(v___x_262_);
lean_dec(v___x_259_);
return v___x_263_;
}
v___jp_265_:
{
lean_object* v_max_267_; uint8_t v___x_268_; 
v_max_267_ = l_Std_Time_Month_Ordinal_days(v___y_266_, v_month_212_);
v___x_268_ = lean_int_dec_lt(v_max_267_, v___x_264_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v_max_267_);
v___x_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_269_, 0, v_year_211_);
lean_ctor_set(v___x_269_, 1, v_month_212_);
lean_ctor_set(v___x_269_, 2, v___x_264_);
v___y_251_ = v___x_269_;
goto v___jp_250_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_270_, 0, v_year_211_);
lean_ctor_set(v___x_270_, 1, v_month_212_);
lean_ctor_set(v___x_270_, 2, v_max_267_);
v___y_251_ = v___x_270_;
goto v___jp_250_;
}
}
v___jp_274_:
{
if (v___y_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_277_ = lean_int_mod(v_year_211_, v___x_276_);
v___x_278_ = lean_int_dec_eq(v___x_277_, v___x_273_);
lean_dec(v___x_277_);
if (v___x_278_ == 0)
{
v___y_266_ = v___x_233_;
goto v___jp_265_;
}
else
{
v___y_266_ = v___x_278_;
goto v___jp_265_;
}
}
else
{
v___y_266_ = v___y_275_;
goto v___jp_265_;
}
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_290_; 
v___x_283_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_284_ = lean_int_mod(v_year_211_, v___x_283_);
v___x_285_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_290_ = lean_int_dec_eq(v___x_284_, v___x_285_);
lean_dec(v___x_284_);
if (v___x_290_ == 0)
{
v___y_241_ = v___x_290_;
goto v___jp_240_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_292_ = lean_int_mod(v_year_211_, v___x_291_);
v___x_293_ = lean_int_dec_eq(v___x_292_, v___x_285_);
lean_dec(v___x_292_);
if (v___x_293_ == 0)
{
if (v___x_290_ == 0)
{
goto v___jp_286_;
}
else
{
v___y_241_ = v___x_233_;
goto v___jp_240_;
}
}
else
{
goto v___jp_286_;
}
}
v___jp_286_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_288_ = lean_int_mod(v_year_211_, v___x_287_);
v___x_289_ = lean_int_dec_eq(v___x_288_, v___x_285_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
v___y_241_ = v___x_289_;
goto v___jp_240_;
}
else
{
v___y_241_ = v___x_233_;
goto v___jp_240_;
}
}
}
v___jp_215_:
{
uint8_t v___x_217_; lean_object* v_lastWday_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_inc_ref(v___y_216_);
v___x_217_ = l_Std_Time_PlainDate_weekday(v___y_216_);
v_lastWday_218_ = l_Std_Time_Weekday_toOrdinal(v___x_217_);
v___x_219_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_220_ = lean_int_neg(v_day_214_);
v___x_221_ = lean_int_add(v_lastWday_218_, v___x_220_);
lean_dec(v___x_220_);
lean_dec(v_lastWday_218_);
v___x_222_ = lean_int_emod(v___x_221_, v___x_219_);
lean_dec(v___x_221_);
v___x_223_ = l_Std_Time_PlainDate_toEpochDay(v___y_216_);
v___x_224_ = lean_int_sub(v___x_223_, v___x_222_);
lean_dec(v___x_222_);
lean_dec(v___x_223_);
return v___x_224_;
}
v___jp_225_:
{
lean_object* v_max_228_; uint8_t v___x_229_; 
v_max_228_ = l_Std_Time_Month_Ordinal_days(v___y_227_, v_month_212_);
v___x_229_ = lean_int_dec_lt(v_max_228_, v___y_226_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_dec(v_max_228_);
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v_year_211_);
lean_ctor_set(v___x_230_, 1, v_month_212_);
lean_ctor_set(v___x_230_, 2, v___y_226_);
v___y_216_ = v___x_230_;
goto v___jp_215_;
}
else
{
lean_object* v___x_231_; 
lean_dec(v___y_226_);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v_year_211_);
lean_ctor_set(v___x_231_, 1, v_month_212_);
lean_ctor_set(v___x_231_, 2, v_max_228_);
v___y_216_ = v___x_231_;
goto v___jp_215_;
}
}
v___jp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_238_ = lean_int_mod(v_year_211_, v___x_237_);
v___x_239_ = lean_int_dec_eq(v___x_238_, v___y_235_);
lean_dec(v___x_238_);
if (v___x_239_ == 0)
{
v___y_226_ = v___y_236_;
v___y_227_ = v___x_239_;
goto v___jp_225_;
}
else
{
v___y_226_ = v___y_236_;
v___y_227_ = v___x_233_;
goto v___jp_225_;
}
}
v___jp_240_:
{
lean_object* v_lastDay_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_lastDay_242_ = l_Std_Time_Month_Ordinal_days(v___y_241_, v_month_212_);
v___x_243_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_244_ = lean_int_mod(v_year_211_, v___x_243_);
v___x_245_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_246_ = lean_int_dec_eq(v___x_244_, v___x_245_);
lean_dec(v___x_244_);
if (v___x_246_ == 0)
{
v___y_226_ = v_lastDay_242_;
v___y_227_ = v___x_246_;
goto v___jp_225_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_248_ = lean_int_mod(v_year_211_, v___x_247_);
v___x_249_ = lean_int_dec_eq(v___x_248_, v___x_245_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
if (v___x_246_ == 0)
{
v___y_235_ = v___x_245_;
v___y_236_ = v_lastDay_242_;
goto v___jp_234_;
}
else
{
v___y_226_ = v_lastDay_242_;
v___y_227_ = v___x_233_;
goto v___jp_225_;
}
}
else
{
v___y_235_ = v___x_245_;
v___y_236_ = v_lastDay_242_;
goto v___jp_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___boxed(lean_object* v_year_294_, lean_object* v_month_295_, lean_object* v_week_296_, lean_object* v_day_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(v_year_294_, v_month_295_, v_week_296_, v_day_297_);
lean_dec(v_day_297_);
lean_dec(v_week_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__0(lean_object* v_a_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_nat_to_int(v_a_299_);
v___x_301_ = l_Rat_ofInt(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(60u);
v___x_303_ = lean_nat_to_int(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(11u);
v___x_305_ = lean_nat_to_int(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1);
v___x_307_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_308_ = lean_int_add(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_310_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2);
v___x_311_ = lean_int_sub(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_range_314_; 
v___x_312_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_313_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3);
v_range_314_ = lean_int_add(v___x_313_, v___x_312_);
return v_range_314_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5(void){
_start:
{
lean_object* v_range_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_range_315_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_316_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10);
v___x_317_ = lean_int_emod(v___x_316_, v_range_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6(void){
_start:
{
lean_object* v_range_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_range_318_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_319_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5);
v___x_320_ = lean_int_add(v___x_319_, v_range_318_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7(void){
_start:
{
lean_object* v_range_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_range_321_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_322_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6);
v___x_323_ = lean_int_emod(v___x_322_, v_range_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_325_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7);
v___x_326_ = lean_int_add(v___x_325_, v___x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(lean_object* v_year_327_, lean_object* v_day_328_){
_start:
{
lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_338_; lean_object* v___y_341_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_352_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___y_363_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_375_; 
v___x_360_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8);
v___x_361_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_368_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_369_ = lean_int_mod(v_year_327_, v___x_368_);
v___x_370_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_375_ = lean_int_dec_eq(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
if (v___x_375_ == 0)
{
v___y_363_ = v___x_375_;
goto v___jp_362_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_377_ = lean_int_mod(v_year_327_, v___x_376_);
v___x_378_ = lean_int_dec_eq(v___x_377_, v___x_370_);
lean_dec(v___x_377_);
if (v___x_378_ == 0)
{
if (v___x_375_ == 0)
{
goto v___jp_371_;
}
else
{
v___y_363_ = v___x_375_;
goto v___jp_362_;
}
}
else
{
goto v___jp_371_;
}
}
v___jp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_332_ = l_Std_Time_PlainDate_toEpochDay(v___y_330_);
v___x_333_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_334_ = lean_int_sub(v_day_328_, v___x_333_);
v___x_335_ = lean_int_add(v___x_334_, v___y_331_);
lean_dec(v___x_334_);
v___x_336_ = lean_int_add(v___x_332_, v___x_335_);
lean_dec(v___x_335_);
lean_dec(v___x_332_);
return v___x_336_;
}
v___jp_337_:
{
lean_object* v___x_339_; 
v___x_339_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___y_330_ = v___y_338_;
v___y_331_ = v___x_339_;
goto v___jp_329_;
}
v___jp_340_:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0);
v___x_343_ = lean_int_dec_le(v___x_342_, v_day_328_);
if (v___x_343_ == 0)
{
v___y_338_ = v___y_341_;
goto v___jp_337_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_330_ = v___y_341_;
v___y_331_ = v___x_344_;
goto v___jp_329_;
}
}
v___jp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_348_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_349_ = lean_int_mod(v_year_327_, v___x_348_);
lean_dec(v_year_327_);
v___x_350_ = lean_int_dec_eq(v___x_349_, v___y_347_);
lean_dec(v___x_349_);
if (v___x_350_ == 0)
{
v___y_338_ = v___y_346_;
goto v___jp_337_;
}
else
{
v___y_341_ = v___y_346_;
goto v___jp_340_;
}
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_353_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_354_ = lean_int_mod(v_year_327_, v___x_353_);
v___x_355_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_356_ = lean_int_dec_eq(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
if (v___x_356_ == 0)
{
lean_dec(v_year_327_);
v___y_338_ = v___y_352_;
goto v___jp_337_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_358_ = lean_int_mod(v_year_327_, v___x_357_);
v___x_359_ = lean_int_dec_eq(v___x_358_, v___x_355_);
lean_dec(v___x_358_);
if (v___x_359_ == 0)
{
if (v___x_356_ == 0)
{
v___y_346_ = v___y_352_;
v___y_347_ = v___x_355_;
goto v___jp_345_;
}
else
{
lean_dec(v_year_327_);
v___y_341_ = v___y_352_;
goto v___jp_340_;
}
}
else
{
v___y_346_ = v___y_352_;
v___y_347_ = v___x_355_;
goto v___jp_345_;
}
}
}
v___jp_362_:
{
lean_object* v_max_364_; uint8_t v___x_365_; 
v_max_364_ = l_Std_Time_Month_Ordinal_days(v___y_363_, v___x_360_);
v___x_365_ = lean_int_dec_lt(v_max_364_, v___x_361_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_max_364_);
lean_inc(v_year_327_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_year_327_);
lean_ctor_set(v___x_366_, 1, v___x_360_);
lean_ctor_set(v___x_366_, 2, v___x_361_);
v___y_352_ = v___x_366_;
goto v___jp_351_;
}
else
{
lean_object* v___x_367_; 
lean_inc(v_year_327_);
v___x_367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_367_, 0, v_year_327_);
lean_ctor_set(v___x_367_, 1, v___x_360_);
lean_ctor_set(v___x_367_, 2, v_max_364_);
v___y_352_ = v___x_367_;
goto v___jp_351_;
}
}
v___jp_371_:
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_373_ = lean_int_mod(v_year_327_, v___x_372_);
v___x_374_ = lean_int_dec_eq(v___x_373_, v___x_370_);
lean_dec(v___x_373_);
v___y_363_ = v___x_374_;
goto v___jp_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___boxed(lean_object* v_year_379_, lean_object* v_day_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(v_year_379_, v_day_380_);
lean_dec(v_day_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(lean_object* v_year_382_, lean_object* v_day_383_){
_start:
{
lean_object* v___y_385_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___y_391_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_403_; 
v___x_388_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8);
v___x_389_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_396_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_397_ = lean_int_mod(v_year_382_, v___x_396_);
v___x_398_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_403_ = lean_int_dec_eq(v___x_397_, v___x_398_);
lean_dec(v___x_397_);
if (v___x_403_ == 0)
{
v___y_391_ = v___x_403_;
goto v___jp_390_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_405_ = lean_int_mod(v_year_382_, v___x_404_);
v___x_406_ = lean_int_dec_eq(v___x_405_, v___x_398_);
lean_dec(v___x_405_);
if (v___x_406_ == 0)
{
if (v___x_403_ == 0)
{
goto v___jp_399_;
}
else
{
v___y_391_ = v___x_403_;
goto v___jp_390_;
}
}
else
{
goto v___jp_399_;
}
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = l_Std_Time_PlainDate_toEpochDay(v___y_385_);
v___x_387_ = lean_int_add(v___x_386_, v_day_383_);
lean_dec(v___x_386_);
return v___x_387_;
}
v___jp_390_:
{
lean_object* v_max_392_; uint8_t v___x_393_; 
v_max_392_ = l_Std_Time_Month_Ordinal_days(v___y_391_, v___x_388_);
v___x_393_ = lean_int_dec_lt(v_max_392_, v___x_389_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec(v_max_392_);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v_year_382_);
lean_ctor_set(v___x_394_, 1, v___x_388_);
lean_ctor_set(v___x_394_, 2, v___x_389_);
v___y_385_ = v___x_394_;
goto v___jp_384_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_395_, 0, v_year_382_);
lean_ctor_set(v___x_395_, 1, v___x_388_);
lean_ctor_set(v___x_395_, 2, v_max_392_);
v___y_385_ = v___x_395_;
goto v___jp_384_;
}
}
v___jp_399_:
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_401_ = lean_int_mod(v_year_382_, v___x_400_);
v___x_402_ = lean_int_dec_eq(v___x_401_, v___x_398_);
lean_dec(v___x_401_);
v___y_391_ = v___x_402_;
goto v___jp_390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0___boxed(lean_object* v_year_407_, lean_object* v_day_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(v_year_407_, v_day_408_);
lean_dec(v_day_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDay(lean_object* v_spec_410_, lean_object* v_year_411_){
_start:
{
switch(lean_obj_tag(v_spec_410_))
{
case 0:
{
lean_object* v_month_412_; lean_object* v_week_413_; lean_object* v_day_414_; lean_object* v___x_415_; 
v_month_412_ = lean_ctor_get(v_spec_410_, 0);
lean_inc(v_month_412_);
v_week_413_ = lean_ctor_get(v_spec_410_, 1);
lean_inc(v_week_413_);
v_day_414_ = lean_ctor_get(v_spec_410_, 2);
lean_inc(v_day_414_);
lean_dec_ref_known(v_spec_410_, 3);
v___x_415_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(v_year_411_, v_month_412_, v_week_413_, v_day_414_);
lean_dec(v_day_414_);
lean_dec(v_week_413_);
return v___x_415_;
}
case 1:
{
lean_object* v_day_416_; lean_object* v___x_417_; 
v_day_416_ = lean_ctor_get(v_spec_410_, 0);
lean_inc(v_day_416_);
lean_dec_ref_known(v_spec_410_, 1);
v___x_417_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(v_year_411_, v_day_416_);
lean_dec(v_day_416_);
return v___x_417_;
}
default: 
{
lean_object* v_day_418_; lean_object* v___x_419_; 
v_day_418_ = lean_ctor_get(v_spec_410_, 0);
lean_inc(v_day_418_);
lean_dec_ref_known(v_spec_410_, 1);
v___x_419_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(v_year_411_, v_day_418_);
lean_dec(v_day_418_);
return v___x_419_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(8u);
v___x_434_ = lean_nat_to_int(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0));
v___x_443_ = lean_string_length(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13);
v___x_445_ = lean_nat_to_int(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(lean_object* v_x_450_){
_start:
{
lean_object* v_spec_451_; lean_object* v_time_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_485_; 
v_spec_451_ = lean_ctor_get(v_x_450_, 0);
v_time_452_ = lean_ctor_get(v_x_450_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_485_ == 0)
{
v___x_454_ = v_x_450_;
v_isShared_455_ = v_isSharedCheck_485_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_time_452_);
lean_inc(v_spec_451_);
lean_dec(v_x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_485_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_456_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_457_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__6));
v___x_458_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = l_Std_Time_TimeZone_instReprTransitionSpec_repr(v_spec_451_, v___x_459_);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 4);
lean_ctor_set(v___x_454_, 1, v___x_460_);
lean_ctor_set(v___x_454_, 0, v___x_458_);
v___x_462_ = v___x_454_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_484_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_463_ = 0;
v___x_464_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*1, v___x_463_);
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_457_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_box(1);
v___x_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__11));
v___x_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_456_);
v___x_473_ = l_Std_Time_Second_instReprOffset___lam__0(v_time_452_, v___x_459_);
lean_dec(v_time_452_);
v___x_474_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_458_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1, v___x_463_);
v___x_476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_472_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_478_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_476_);
v___x_480_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_477_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*1, v___x_463_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr(lean_object* v_x_486_, lean_object* v_prec_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(v_x_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___boxed(lean_object* v_x_489_, lean_object* v_prec_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Time_TimeZone_instReprTransitionRule_repr(v_x_489_, v_prec_490_);
lean_dec(v_prec_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1));
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_val_503_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_x_500_, 1);
v___x_504_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3));
v___x_505_ = l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(v_val_503_);
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Repr_addAppParen(v___x_506_, v_x_501_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___boxed(lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_x_508_, v_x_509_);
lean_dec(v_x_509_);
return v_res_510_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(10u);
v___x_524_ = lean_nat_to_int(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(9u);
v___x_529_ = lean_nat_to_int(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(lean_object* v_x_533_){
_start:
{
lean_object* v_name_534_; lean_object* v_offset_535_; lean_object* v_start_536_; lean_object* v_end___537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_name_534_ = lean_ctor_get(v_x_533_, 0);
lean_inc_ref(v_name_534_);
v_offset_535_ = lean_ctor_get(v_x_533_, 1);
lean_inc(v_offset_535_);
v_start_536_ = lean_ctor_get(v_x_533_, 2);
lean_inc(v_start_536_);
v_end___537_ = lean_ctor_get(v_x_533_, 3);
lean_inc(v_end___537_);
lean_dec_ref(v_x_533_);
v___x_538_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_539_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__3));
v___x_540_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7);
v___x_541_ = l_String_quote(v_name_534_);
v___x_542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_540_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = 0;
v___x_545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_539_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_box(1);
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__5));
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_538_);
v___x_554_ = lean_obj_once(&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_535_);
lean_dec(v_offset_535_);
v___x_557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_554_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*1, v___x_544_);
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_553_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_547_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_549_);
v___x_562_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__8));
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_538_);
v___x_565_ = lean_obj_once(&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9, &l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9_once, _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9);
v___x_566_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_start_536_, v___x_555_);
v___x_567_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*1, v___x_544_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_564_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_547_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_549_);
v___x_572_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__11));
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_538_);
v___x_575_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_end___537_, v___x_555_);
v___x_576_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_540_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*1, v___x_544_);
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_574_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_580_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_578_);
v___x_582_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*1, v___x_544_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(lean_object* v_x_586_, lean_object* v_prec_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(v_x_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___boxed(lean_object* v_x_589_, lean_object* v_prec_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(v_x_589_, v_prec_590_);
lean_dec(v_prec_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1));
return v___x_596_;
}
else
{
lean_object* v_val_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_val_597_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v_x_594_, 1);
v___x_598_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3));
v___x_599_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(v_val_597_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Repr_addAppParen(v___x_600_, v_x_595_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0___boxed(lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(v_x_602_, v_x_603_);
lean_dec(v_x_603_);
return v_res_604_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(13u);
v___x_618_ = lean_nat_to_int(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(lean_object* v_x_622_){
_start:
{
lean_object* v_stdName_623_; lean_object* v_stdOffset_624_; lean_object* v_dst_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_stdName_623_ = lean_ctor_get(v_x_622_, 0);
lean_inc_ref(v_stdName_623_);
v_stdOffset_624_ = lean_ctor_get(v_x_622_, 1);
lean_inc(v_stdOffset_624_);
v_dst_625_ = lean_ctor_get(v_x_622_, 2);
lean_inc(v_dst_625_);
lean_dec_ref(v_x_622_);
v___x_626_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_627_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__3));
v___x_628_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1);
v___x_629_ = l_String_quote(v_stdName_623_);
v___x_630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_632_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_627_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_box(1);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__5));
v___x_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_626_);
v___x_642_ = lean_obj_once(&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_stdOffset_624_);
lean_dec(v_stdOffset_624_);
v___x_645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_642_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_632_);
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_641_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_635_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_637_);
v___x_650_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__8));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_626_);
v___x_653_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_654_ = l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(v_dst_625_, v___x_643_);
v___x_655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v___x_632_);
v___x_657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_652_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_659_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_657_);
v___x_661_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_658_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_632_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr(lean_object* v_x_665_, lean_object* v_prec_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_x_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___boxed(lean_object* v_x_668_, lean_object* v_prec_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_Time_TimeZone_instReprRecurringRule_repr(v_x_668_, v_prec_669_);
lean_dec(v_prec_669_);
return v_res_670_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Week(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
