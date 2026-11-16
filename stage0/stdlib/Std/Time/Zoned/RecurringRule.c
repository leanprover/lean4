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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Time_TimeZone_TransitionSpec_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_month_7_; lean_object* v_week_8_; lean_object* v_day_9_; lean_object* v___x_10_; 
v_month_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_month_7_);
v_week_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_week_8_);
v_day_9_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_day_9_);
lean_dec_ref_known(v_t_5_, 3);
v___x_10_ = lean_apply_3(v_k_6_, v_month_7_, v_week_8_, v_day_9_);
return v___x_10_;
}
else
{
lean_object* v_day_11_; lean_object* v___x_12_; 
v_day_11_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_day_11_);
lean_dec_ref(v_t_5_);
v___x_12_ = lean_apply_1(v_k_6_, v_day_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_mwd_elim___redArg(lean_object* v_t_25_, lean_object* v_mwd_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_25_, v_mwd_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_mwd_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_mwd_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_29_, v_mwd_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian_elim___redArg(lean_object* v_t_33_, lean_object* v_julian_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_33_, v_julian_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_julian_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_37_, v_julian_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian0_elim___redArg(lean_object* v_t_41_, lean_object* v_julian0_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_41_, v_julian0_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_julian0_elim(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_julian0_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Time_TimeZone_TransitionSpec_ctorElim___redArg(v_t_45_, v_julian0_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(2u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_nat_to_int(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr(lean_object* v_x_73_, lean_object* v_prec_74_){
_start:
{
lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; 
switch(lean_obj_tag(v_x_73_))
{
case 0:
{
lean_object* v_month_93_; lean_object* v_week_94_; lean_object* v_day_95_; lean_object* v___y_97_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_month_93_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_month_93_);
v_week_94_ = lean_ctor_get(v_x_73_, 1);
lean_inc(v_week_94_);
v_day_95_ = lean_ctor_get(v_x_73_, 2);
lean_inc(v_day_95_);
lean_dec_ref_known(v_x_73_, 3);
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = lean_nat_dec_le(v___x_113_, v_prec_74_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3);
v___y_97_ = v___x_115_;
goto v___jp_96_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_97_ = v___x_116_;
goto v___jp_96_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_98_ = lean_box(1);
v___x_99_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__2));
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = l_Std_Time_Month_instReprOrdinal___lam__0(v_month_93_, v___x_100_);
lean_dec(v_month_93_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_99_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_98_);
v___x_104_ = l_Std_Time_Week_instReprOffset___lam__0(v_week_94_, v___x_100_);
lean_dec(v_week_94_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_98_);
v___x_107_ = l_Std_Time_Weekday_instReprOrdinal___lam__0(v_day_95_, v___x_100_);
lean_dec(v_day_95_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
lean_inc(v___y_97_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_97_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_74_);
return v___x_112_;
}
}
case 1:
{
lean_object* v_day_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_140_; 
v_day_117_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_140_ == 0)
{
v___x_119_ = v_x_73_;
v_isShared_120_ = v_isSharedCheck_140_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_day_117_);
lean_dec(v_x_73_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_140_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___y_122_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1024u);
v___x_137_ = lean_nat_dec_le(v___x_136_, v_prec_74_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3);
v___y_122_ = v___x_138_;
goto v___jp_121_;
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_122_ = v___x_139_;
goto v___jp_121_;
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__7));
v___x_124_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_125_ = lean_int_dec_lt(v_day_117_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = l_Int_repr(v_day_117_);
lean_dec(v_day_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 3);
lean_ctor_set(v___x_119_, 0, v___x_126_);
v___x_128_ = v___x_119_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v___y_85_ = v___x_123_;
v___y_86_ = v___y_122_;
v___y_87_ = v___x_128_;
goto v___jp_84_;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_unsigned_to_nat(1024u);
v___x_131_ = l_Int_repr(v_day_117_);
lean_dec(v_day_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 3);
lean_ctor_set(v___x_119_, 0, v___x_131_);
v___x_133_ = v___x_119_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = l_Repr_addAppParen(v___x_133_, v___x_130_);
v___y_85_ = v___x_123_;
v___y_86_ = v___y_122_;
v___y_87_ = v___x_134_;
goto v___jp_84_;
}
}
}
}
}
default: 
{
lean_object* v_day_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_164_; 
v_day_141_ = lean_ctor_get(v_x_73_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_164_ == 0)
{
v___x_143_ = v_x_73_;
v_isShared_144_ = v_isSharedCheck_164_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_day_141_);
lean_dec(v_x_73_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_164_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___y_146_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(1024u);
v___x_161_ = lean_nat_dec_le(v___x_160_, v_prec_74_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__3);
v___y_146_ = v___x_162_;
goto v___jp_145_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_146_ = v___x_163_;
goto v___jp_145_;
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__11));
v___x_148_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_149_ = lean_int_dec_lt(v_day_141_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = l_Int_repr(v_day_141_);
lean_dec(v_day_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 3);
lean_ctor_set(v___x_143_, 0, v___x_150_);
v___x_152_ = v___x_143_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v___y_76_ = v___y_146_;
v___y_77_ = v___x_147_;
v___y_78_ = v___x_152_;
goto v___jp_75_;
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = lean_unsigned_to_nat(1024u);
v___x_155_ = l_Int_repr(v_day_141_);
lean_dec(v_day_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 3);
lean_ctor_set(v___x_143_, 0, v___x_155_);
v___x_157_ = v___x_143_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = l_Repr_addAppParen(v___x_157_, v___x_154_);
v___y_76_ = v___y_146_;
v___y_77_ = v___x_147_;
v___y_78_ = v___x_158_;
goto v___jp_75_;
}
}
}
}
}
}
v___jp_75_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc(v___y_77_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___y_77_);
lean_ctor_set(v___x_79_, 1, v___y_78_);
lean_inc(v___y_76_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_76_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v_prec_74_);
return v___x_83_;
}
v___jp_84_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_inc(v___y_85_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___y_85_);
lean_ctor_set(v___x_88_, 1, v___y_87_);
lean_inc(v___y_86_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_86_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_74_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionSpec_repr___boxed(lean_object* v_x_165_, lean_object* v_prec_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Time_TimeZone_instReprTransitionSpec_repr(v_x_165_, v_prec_166_);
lean_dec(v_prec_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__1(lean_object* v_a_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_nat_to_int(v_a_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(7u);
v___x_173_ = lean_nat_to_int(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(4u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(100u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(400u);
v___x_179_ = lean_nat_to_int(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(5u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_183_ = lean_int_neg(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(30u);
v___x_185_ = lean_nat_to_int(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__6);
v___x_187_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_188_ = lean_int_add(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_190_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__7);
v___x_191_ = lean_int_sub(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_range_194_; 
v___x_192_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_193_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__8);
v_range_194_ = lean_int_add(v___x_193_, v___x_192_);
return v_range_194_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_196_ = lean_int_sub(v___x_195_, v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11(void){
_start:
{
lean_object* v_range_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_range_197_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_198_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10);
v___x_199_ = lean_int_emod(v___x_198_, v_range_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12(void){
_start:
{
lean_object* v_range_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_range_200_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_201_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__11);
v___x_202_ = lean_int_add(v___x_201_, v_range_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13(void){
_start:
{
lean_object* v_range_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_range_203_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__9);
v___x_204_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__12);
v___x_205_ = lean_int_emod(v___x_204_, v_range_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_207_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__13);
v___x_208_ = lean_int_add(v___x_207_, v___x_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(lean_object* v_year_209_, lean_object* v_month_210_, lean_object* v_week_211_, lean_object* v_day_212_){
_start:
{
lean_object* v___y_214_; lean_object* v___y_224_; uint8_t v___y_225_; uint8_t v___y_231_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__4);
v___x_244_ = lean_int_dec_eq(v_week_211_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___y_246_; lean_object* v___x_259_; uint8_t v___y_261_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_259_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_266_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_267_ = lean_int_mod(v_year_209_, v___x_266_);
v___x_268_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_269_ = lean_int_dec_eq(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
if (v___x_269_ == 0)
{
v___y_261_ = v___x_269_;
goto v___jp_260_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_271_ = lean_int_mod(v_year_209_, v___x_270_);
v___x_272_ = lean_int_dec_eq(v___x_271_, v___x_268_);
lean_dec(v___x_271_);
if (v___x_272_ == 0)
{
v___y_261_ = v___x_269_;
goto v___jp_260_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_274_ = lean_int_mod(v_year_209_, v___x_273_);
v___x_275_ = lean_int_dec_eq(v___x_274_, v___x_268_);
lean_dec(v___x_274_);
v___y_261_ = v___x_275_;
goto v___jp_260_;
}
}
v___jp_245_:
{
uint8_t v___x_247_; lean_object* v_firstWday_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_firstOccurrence_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_extra_257_; lean_object* v___x_258_; 
lean_inc_ref(v___y_246_);
v___x_247_ = l_Std_Time_PlainDate_weekday(v___y_246_);
v_firstWday_248_ = l_Std_Time_Weekday_toOrdinal(v___x_247_);
v___x_249_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_250_ = lean_int_neg(v_firstWday_248_);
lean_dec(v_firstWday_248_);
v___x_251_ = lean_int_add(v_day_212_, v___x_250_);
lean_dec(v___x_250_);
v___x_252_ = lean_int_emod(v___x_251_, v___x_249_);
lean_dec(v___x_251_);
v___x_253_ = l_Std_Time_PlainDate_toEpochDay(v___y_246_);
v_firstOccurrence_254_ = lean_int_add(v___x_253_, v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_253_);
v___x_255_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__5);
v___x_256_ = lean_int_add(v_week_211_, v___x_255_);
v_extra_257_ = lean_int_mul(v___x_256_, v___x_249_);
lean_dec(v___x_256_);
v___x_258_ = lean_int_add(v_firstOccurrence_254_, v_extra_257_);
lean_dec(v_extra_257_);
lean_dec(v_firstOccurrence_254_);
return v___x_258_;
}
v___jp_260_:
{
lean_object* v_max_262_; uint8_t v___x_263_; 
v_max_262_ = l_Std_Time_Month_Ordinal_days(v___y_261_, v_month_210_);
v___x_263_ = lean_int_dec_lt(v_max_262_, v___x_259_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v_max_262_);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v_year_209_);
lean_ctor_set(v___x_264_, 1, v_month_210_);
lean_ctor_set(v___x_264_, 2, v___x_259_);
v___y_246_ = v___x_264_;
goto v___jp_245_;
}
else
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_265_, 0, v_year_209_);
lean_ctor_set(v___x_265_, 1, v_month_210_);
lean_ctor_set(v___x_265_, 2, v_max_262_);
v___y_246_ = v___x_265_;
goto v___jp_245_;
}
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_276_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_277_ = lean_int_mod(v_year_209_, v___x_276_);
v___x_278_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_279_ = lean_int_dec_eq(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
if (v___x_279_ == 0)
{
v___y_231_ = v___x_279_;
goto v___jp_230_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_281_ = lean_int_mod(v_year_209_, v___x_280_);
v___x_282_ = lean_int_dec_eq(v___x_281_, v___x_278_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
v___y_231_ = v___x_279_;
goto v___jp_230_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_284_ = lean_int_mod(v_year_209_, v___x_283_);
v___x_285_ = lean_int_dec_eq(v___x_284_, v___x_278_);
lean_dec(v___x_284_);
v___y_231_ = v___x_285_;
goto v___jp_230_;
}
}
}
v___jp_213_:
{
uint8_t v___x_215_; lean_object* v_lastWday_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v___y_214_);
v___x_215_ = l_Std_Time_PlainDate_weekday(v___y_214_);
v_lastWday_216_ = l_Std_Time_Weekday_toOrdinal(v___x_215_);
v___x_217_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_218_ = lean_int_neg(v_day_212_);
v___x_219_ = lean_int_add(v_lastWday_216_, v___x_218_);
lean_dec(v___x_218_);
lean_dec(v_lastWday_216_);
v___x_220_ = lean_int_emod(v___x_219_, v___x_217_);
lean_dec(v___x_219_);
v___x_221_ = l_Std_Time_PlainDate_toEpochDay(v___y_214_);
v___x_222_ = lean_int_sub(v___x_221_, v___x_220_);
lean_dec(v___x_220_);
lean_dec(v___x_221_);
return v___x_222_;
}
v___jp_223_:
{
lean_object* v_max_226_; uint8_t v___x_227_; 
v_max_226_ = l_Std_Time_Month_Ordinal_days(v___y_225_, v_month_210_);
v___x_227_ = lean_int_dec_lt(v_max_226_, v___y_224_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v_max_226_);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v_year_209_);
lean_ctor_set(v___x_228_, 1, v_month_210_);
lean_ctor_set(v___x_228_, 2, v___y_224_);
v___y_214_ = v___x_228_;
goto v___jp_213_;
}
else
{
lean_object* v___x_229_; 
lean_dec(v___y_224_);
v___x_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_229_, 0, v_year_209_);
lean_ctor_set(v___x_229_, 1, v_month_210_);
lean_ctor_set(v___x_229_, 2, v_max_226_);
v___y_214_ = v___x_229_;
goto v___jp_213_;
}
}
v___jp_230_:
{
lean_object* v_lastDay_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_lastDay_232_ = l_Std_Time_Month_Ordinal_days(v___y_231_, v_month_210_);
v___x_233_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_234_ = lean_int_mod(v_year_209_, v___x_233_);
v___x_235_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_236_ = lean_int_dec_eq(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
if (v___x_236_ == 0)
{
v___y_224_ = v_lastDay_232_;
v___y_225_ = v___x_236_;
goto v___jp_223_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_238_ = lean_int_mod(v_year_209_, v___x_237_);
v___x_239_ = lean_int_dec_eq(v___x_238_, v___x_235_);
lean_dec(v___x_238_);
if (v___x_239_ == 0)
{
v___y_224_ = v_lastDay_232_;
v___y_225_ = v___x_236_;
goto v___jp_223_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_241_ = lean_int_mod(v_year_209_, v___x_240_);
v___x_242_ = lean_int_dec_eq(v___x_241_, v___x_235_);
lean_dec(v___x_241_);
v___y_224_ = v_lastDay_232_;
v___y_225_ = v___x_242_;
goto v___jp_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___boxed(lean_object* v_year_286_, lean_object* v_month_287_, lean_object* v_week_288_, lean_object* v_day_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(v_year_286_, v_month_287_, v_week_288_, v_day_289_);
lean_dec(v_day_289_);
lean_dec(v_week_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TransitionSpec_toEpochDayMWD_spec__0(lean_object* v_a_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_nat_to_int(v_a_291_);
v___x_293_ = l_Rat_ofInt(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(60u);
v___x_295_ = lean_nat_to_int(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(11u);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1);
v___x_299_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_300_ = lean_int_add(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_302_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__2);
v___x_303_ = lean_int_sub(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_range_306_; 
v___x_304_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_305_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__3);
v_range_306_ = lean_int_add(v___x_305_, v___x_304_);
return v_range_306_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5(void){
_start:
{
lean_object* v_range_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_range_307_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_308_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__10);
v___x_309_ = lean_int_emod(v___x_308_, v_range_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6(void){
_start:
{
lean_object* v_range_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_range_310_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_311_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__5);
v___x_312_ = lean_int_add(v___x_311_, v_range_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7(void){
_start:
{
lean_object* v_range_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_range_313_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__4);
v___x_314_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__6);
v___x_315_ = lean_int_emod(v___x_314_, v_range_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_317_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__7);
v___x_318_ = lean_int_add(v___x_317_, v___x_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(lean_object* v_year_319_, lean_object* v_day_320_){
_start:
{
lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_330_; lean_object* v___y_333_; lean_object* v___y_338_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___y_352_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_349_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8);
v___x_350_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_357_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_358_ = lean_int_mod(v_year_319_, v___x_357_);
v___x_359_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_360_ = lean_int_dec_eq(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
if (v___x_360_ == 0)
{
v___y_352_ = v___x_360_;
goto v___jp_351_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_362_ = lean_int_mod(v_year_319_, v___x_361_);
v___x_363_ = lean_int_dec_eq(v___x_362_, v___x_359_);
lean_dec(v___x_362_);
if (v___x_363_ == 0)
{
v___y_352_ = v___x_360_;
goto v___jp_351_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_364_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_365_ = lean_int_mod(v_year_319_, v___x_364_);
v___x_366_ = lean_int_dec_eq(v___x_365_, v___x_359_);
lean_dec(v___x_365_);
v___y_352_ = v___x_366_;
goto v___jp_351_;
}
}
v___jp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = l_Std_Time_PlainDate_toEpochDay(v___y_322_);
v___x_325_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___x_326_ = lean_int_sub(v_day_320_, v___x_325_);
v___x_327_ = lean_int_add(v___x_326_, v___y_323_);
lean_dec(v___x_326_);
v___x_328_ = lean_int_add(v___x_324_, v___x_327_);
lean_dec(v___x_327_);
lean_dec(v___x_324_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___y_322_ = v___y_330_;
v___y_323_ = v___x_331_;
goto v___jp_321_;
}
v___jp_332_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__0);
v___x_335_ = lean_int_dec_le(v___x_334_, v_day_320_);
if (v___x_335_ == 0)
{
v___y_330_ = v___y_333_;
goto v___jp_329_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__4);
v___y_322_ = v___y_333_;
v___y_323_ = v___x_336_;
goto v___jp_321_;
}
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_339_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_340_ = lean_int_mod(v_year_319_, v___x_339_);
v___x_341_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_342_ = lean_int_dec_eq(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
if (v___x_342_ == 0)
{
lean_dec(v_year_319_);
v___y_330_ = v___y_338_;
goto v___jp_329_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_344_ = lean_int_mod(v_year_319_, v___x_343_);
v___x_345_ = lean_int_dec_eq(v___x_344_, v___x_341_);
lean_dec(v___x_344_);
if (v___x_345_ == 0)
{
lean_dec(v_year_319_);
v___y_333_ = v___y_338_;
goto v___jp_332_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_347_ = lean_int_mod(v_year_319_, v___x_346_);
lean_dec(v_year_319_);
v___x_348_ = lean_int_dec_eq(v___x_347_, v___x_341_);
lean_dec(v___x_347_);
if (v___x_348_ == 0)
{
v___y_330_ = v___y_338_;
goto v___jp_329_;
}
else
{
v___y_333_ = v___y_338_;
goto v___jp_332_;
}
}
}
}
v___jp_351_:
{
lean_object* v_max_353_; uint8_t v___x_354_; 
v_max_353_ = l_Std_Time_Month_Ordinal_days(v___y_352_, v___x_349_);
v___x_354_ = lean_int_dec_lt(v_max_353_, v___x_350_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec(v_max_353_);
lean_inc(v_year_319_);
v___x_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_355_, 0, v_year_319_);
lean_ctor_set(v___x_355_, 1, v___x_349_);
lean_ctor_set(v___x_355_, 2, v___x_350_);
v___y_338_ = v___x_355_;
goto v___jp_337_;
}
else
{
lean_object* v___x_356_; 
lean_inc(v_year_319_);
v___x_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_356_, 0, v_year_319_);
lean_ctor_set(v___x_356_, 1, v___x_349_);
lean_ctor_set(v___x_356_, 2, v_max_353_);
v___y_338_ = v___x_356_;
goto v___jp_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___boxed(lean_object* v_year_367_, lean_object* v_day_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(v_year_367_, v_day_368_);
lean_dec(v_day_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(lean_object* v_year_370_, lean_object* v_day_371_){
_start:
{
lean_object* v___y_373_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___y_379_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_376_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__8);
v___x_377_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__14);
v___x_384_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__1);
v___x_385_ = lean_int_mod(v_year_370_, v___x_384_);
v___x_386_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8, &l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8_once, _init_l_Std_Time_TimeZone_instReprTransitionSpec_repr___closed__8);
v___x_387_ = lean_int_dec_eq(v___x_385_, v___x_386_);
lean_dec(v___x_385_);
if (v___x_387_ == 0)
{
v___y_379_ = v___x_387_;
goto v___jp_378_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__2);
v___x_389_ = lean_int_mod(v_year_370_, v___x_388_);
v___x_390_ = lean_int_dec_eq(v___x_389_, v___x_386_);
lean_dec(v___x_389_);
if (v___x_390_ == 0)
{
v___y_379_ = v___x_387_;
goto v___jp_378_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__3);
v___x_392_ = lean_int_mod(v_year_370_, v___x_391_);
v___x_393_ = lean_int_dec_eq(v___x_392_, v___x_386_);
lean_dec(v___x_392_);
v___y_379_ = v___x_393_;
goto v___jp_378_;
}
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_Std_Time_PlainDate_toEpochDay(v___y_373_);
v___x_375_ = lean_int_add(v___x_374_, v_day_371_);
lean_dec(v___x_374_);
return v___x_375_;
}
v___jp_378_:
{
lean_object* v_max_380_; uint8_t v___x_381_; 
v_max_380_ = l_Std_Time_Month_Ordinal_days(v___y_379_, v___x_376_);
v___x_381_ = lean_int_dec_lt(v_max_380_, v___x_377_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v_max_380_);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v_year_370_);
lean_ctor_set(v___x_382_, 1, v___x_376_);
lean_ctor_set(v___x_382_, 2, v___x_377_);
v___y_373_ = v___x_382_;
goto v___jp_372_;
}
else
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_383_, 0, v_year_370_);
lean_ctor_set(v___x_383_, 1, v___x_376_);
lean_ctor_set(v___x_383_, 2, v_max_380_);
v___y_373_ = v___x_383_;
goto v___jp_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0___boxed(lean_object* v_year_394_, lean_object* v_day_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(v_year_394_, v_day_395_);
lean_dec(v_day_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDay(lean_object* v_spec_397_, lean_object* v_year_398_){
_start:
{
switch(lean_obj_tag(v_spec_397_))
{
case 0:
{
lean_object* v_month_399_; lean_object* v_week_400_; lean_object* v_day_401_; lean_object* v___x_402_; 
v_month_399_ = lean_ctor_get(v_spec_397_, 0);
lean_inc(v_month_399_);
v_week_400_ = lean_ctor_get(v_spec_397_, 1);
lean_inc(v_week_400_);
v_day_401_ = lean_ctor_get(v_spec_397_, 2);
lean_inc(v_day_401_);
lean_dec_ref_known(v_spec_397_, 3);
v___x_402_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD(v_year_398_, v_month_399_, v_week_400_, v_day_401_);
lean_dec(v_day_401_);
lean_dec(v_week_400_);
return v___x_402_;
}
case 1:
{
lean_object* v_day_403_; lean_object* v___x_404_; 
v_day_403_ = lean_ctor_get(v_spec_397_, 0);
lean_inc(v_day_403_);
lean_dec_ref_known(v_spec_397_, 1);
v___x_404_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian(v_year_398_, v_day_403_);
lean_dec(v_day_403_);
return v___x_404_;
}
default: 
{
lean_object* v_day_405_; lean_object* v___x_406_; 
v_day_405_ = lean_ctor_get(v_spec_397_, 0);
lean_inc(v_day_405_);
lean_dec_ref_known(v_spec_397_, 1);
v___x_406_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian0(v_year_398_, v_day_405_);
lean_dec(v_day_405_);
return v___x_406_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(8u);
v___x_421_ = lean_nat_to_int(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__0));
v___x_430_ = lean_string_length(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__13);
v___x_432_ = lean_nat_to_int(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(lean_object* v_x_437_){
_start:
{
lean_object* v_spec_438_; lean_object* v_time_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_472_; 
v_spec_438_ = lean_ctor_get(v_x_437_, 0);
v_time_439_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_472_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_472_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_time_439_);
lean_inc(v_spec_438_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_472_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_443_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_444_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__6));
v___x_445_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Std_Time_TimeZone_instReprTransitionSpec_repr(v_spec_438_, v___x_446_);
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 4);
lean_ctor_set(v___x_441_, 1, v___x_447_);
lean_ctor_set(v___x_441_, 0, v___x_445_);
v___x_449_ = v___x_441_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_471_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_444_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_box(1);
v___x_456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__11));
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_443_);
v___x_460_ = l_Std_Time_Second_instReprOffset___lam__0(v_time_439_, v___x_446_);
lean_dec(v_time_439_);
v___x_461_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_445_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_450_);
v___x_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_459_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_465_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_463_);
v___x_467_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_464_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*1, v___x_450_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr(lean_object* v_x_473_, lean_object* v_prec_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(v_x_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransitionRule_repr___boxed(lean_object* v_x_476_, lean_object* v_prec_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Time_TimeZone_instReprTransitionRule_repr(v_x_476_, v_prec_477_);
lean_dec(v_prec_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1));
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_val_490_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_val_490_);
lean_dec_ref_known(v_x_487_, 1);
v___x_491_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3));
v___x_492_ = l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg(v_val_490_);
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Repr_addAppParen(v___x_493_, v_x_488_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___boxed(lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_x_495_, v_x_496_);
lean_dec(v_x_496_);
return v_res_497_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(10u);
v___x_511_ = lean_nat_to_int(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(9u);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(lean_object* v_x_520_){
_start:
{
lean_object* v_name_521_; lean_object* v_offset_522_; lean_object* v_start_523_; lean_object* v_end___524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_name_521_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_name_521_);
v_offset_522_ = lean_ctor_get(v_x_520_, 1);
lean_inc(v_offset_522_);
v_start_523_ = lean_ctor_get(v_x_520_, 2);
lean_inc(v_start_523_);
v_end___524_ = lean_ctor_get(v_x_520_, 3);
lean_inc(v_end___524_);
lean_dec_ref(v_x_520_);
v___x_525_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_526_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__3));
v___x_527_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__7);
v___x_528_ = l_String_quote(v_name_521_);
v___x_529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
v___x_530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_527_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = 0;
v___x_532_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_531_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_526_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_box(1);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__5));
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_525_);
v___x_541_ = lean_obj_once(&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__6);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_522_);
lean_dec(v_offset_522_);
v___x_544_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_531_);
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_540_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_534_);
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_536_);
v___x_549_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__8));
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_525_);
v___x_552_ = lean_obj_once(&l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9, &l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9_once, _init_l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__9);
v___x_553_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_start_523_, v___x_542_);
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*1, v___x_531_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_551_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_534_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_536_);
v___x_559_ = ((lean_object*)(l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg___closed__11));
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_525_);
v___x_562_ = l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0(v_end___524_, v___x_542_);
v___x_563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_527_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*1, v___x_531_);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_561_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_567_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_565_);
v___x_569_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_566_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_531_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(lean_object* v_x_573_, lean_object* v_prec_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(v_x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___boxed(lean_object* v_x_576_, lean_object* v_prec_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr(v_x_576_, v_prec_577_);
lean_dec(v_prec_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__1));
return v___x_583_;
}
else
{
lean_object* v_val_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_val_584_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v_x_581_, 1);
v___x_585_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprDaylightSavingRule_repr_spec__0___closed__3));
v___x_586_ = l_Std_Time_TimeZone_instReprDaylightSavingRule_repr___redArg(v_val_584_);
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Repr_addAppParen(v___x_587_, v_x_582_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0___boxed(lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(v_x_589_, v_x_590_);
lean_dec(v_x_590_);
return v_res_591_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(13u);
v___x_605_ = lean_nat_to_int(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(lean_object* v_x_609_){
_start:
{
lean_object* v_stdName_610_; lean_object* v_stdOffset_611_; lean_object* v_dst_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_stdName_610_ = lean_ctor_get(v_x_609_, 0);
lean_inc_ref(v_stdName_610_);
v_stdOffset_611_ = lean_ctor_get(v_x_609_, 1);
lean_inc(v_stdOffset_611_);
v_dst_612_ = lean_ctor_get(v_x_609_, 2);
lean_inc(v_dst_612_);
lean_dec_ref(v_x_609_);
v___x_613_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__5));
v___x_614_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__3));
v___x_615_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayJulian___closed__1);
v___x_616_ = l_String_quote(v_stdName_610_);
v___x_617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
v___x_618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_615_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = 0;
v___x_620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*1, v___x_619_);
v___x_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_614_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__9));
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_box(1);
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__5));
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_613_);
v___x_629_ = lean_obj_once(&l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__6);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_stdOffset_611_);
lean_dec(v_stdOffset_611_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_629_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_619_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_628_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_622_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_624_);
v___x_637_ = ((lean_object*)(l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg___closed__8));
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_613_);
v___x_640_ = lean_obj_once(&l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0, &l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0_once, _init_l_Std_Time_TimeZone_TransitionSpec_toEpochDayMWD___closed__0);
v___x_641_ = l_Option_repr___at___00Std_Time_TimeZone_instReprRecurringRule_repr_spec__0(v_dst_612_, v___x_630_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_619_);
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_639_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14, &l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__14);
v___x_646_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__15));
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___x_644_);
v___x_648_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransitionRule_repr___redArg___closed__16));
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_645_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*1, v___x_619_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr(lean_object* v_x_652_, lean_object* v_prec_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_x_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___boxed(lean_object* v_x_655_, lean_object* v_prec_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Time_TimeZone_instReprRecurringRule_repr(v_x_655_, v_prec_656_);
lean_dec(v_prec_656_);
return v_res_657_;
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
