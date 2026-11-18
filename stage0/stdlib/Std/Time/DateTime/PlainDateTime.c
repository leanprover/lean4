// Lean compiler output
// Module: Std.Time.DateTime.PlainDateTime
// Imports: public import Std.Time.DateTime.WallTime
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
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainTime_toSeconds(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_withWeekday(lean_object*, uint8_t);
lean_object* l_Std_Time_instReprPlainDate_repr___redArg(lean_object*);
lean_object* l_Std_Time_instReprPlainTime_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Std_Time_instDecidableEqPlainDate_decEq(lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqPlainTime_decEq(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
extern lean_object* l_Std_Time_instOrdPlainDate;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*, uint8_t);
extern lean_object* l_Std_Time_PlainTime_midnight;
extern lean_object* l_Std_Time_instOrdPlainTime;
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedPlainDateTime_default_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__0;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__2;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__3;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__4;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__5;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__6;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__7;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__8;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__9;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__10;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__11;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__12;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__13;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__14;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__15;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__16;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__17;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__18;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__19;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__20;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__21;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__22;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__23;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__24;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__25;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__26;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__27;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__28;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__29;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__30;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__31;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__32;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__33;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__34;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__35;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__36;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__37;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__38;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDateTime_default___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDateTime_default___closed__39;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedPlainDateTime_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedPlainDateTime;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDateTime_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDateTime_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDateTime___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "date"};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "time"};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value;
static lean_once_cell_t l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13;
static lean_once_cell_t l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprPlainDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprPlainDateTime_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprPlainDateTime___closed__0 = (const lean_object*)&l_Std_Time_instReprPlainDateTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprPlainDateTime = (const lean_object*)&l_Std_Time_instReprPlainDateTime___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdPlainDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainDateTime___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDateTime___closed__0 = (const lean_object*)&l_Std_Time_instOrdPlainDateTime___closed__0_value;
static const lean_closure_object l_Std_Time_instOrdPlainDateTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainDateTime___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDateTime___closed__1 = (const lean_object*)&l_Std_Time_instOrdPlainDateTime___closed__1_value;
static lean_once_cell_t l_Std_Time_instOrdPlainDateTime___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDateTime___closed__2;
static lean_once_cell_t l_Std_Time_instOrdPlainDateTime___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDateTime___closed__3;
static lean_once_cell_t l_Std_Time_instOrdPlainDateTime___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDateTime___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime;
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__1(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_toWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toWallTime___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_toWallTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toWallTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_withDaysClip___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_withDaysClip___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_withDaysClip___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_withDaysClip___closed__1;
static lean_once_cell_t l_Std_Time_PlainDateTime_withDaysClip___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_withDaysClip___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_withMilliseconds___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_withMilliseconds___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_addWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_addWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_addMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_addMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__1 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__1 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__2 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__2 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__3 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__3 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__4 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__4 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__5 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__5 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddOffset__6 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubOffset__6 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHAddDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHAddDuration = (const lean_object*)&l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedPlainDateTime_default_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_to_int(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(11u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__2, &l_Std_Time_instInhabitedPlainDateTime_default___closed__2_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__2);
v___x_10_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_11_ = lean_int_add(v___x_10_, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_13_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__3, &l_Std_Time_instInhabitedPlainDateTime_default___closed__3_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__3);
v___x_14_ = lean_int_sub(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_range_17_; 
v___x_15_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_16_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__4, &l_Std_Time_instInhabitedPlainDateTime_default___closed__4_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__4);
v_range_17_ = lean_int_add(v___x_16_, v___x_15_);
return v_range_17_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_19_ = lean_int_sub(v___x_18_, v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__7(void){
_start:
{
lean_object* v_range_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_range_20_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__5, &l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5);
v___x_21_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__6, &l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6);
v___x_22_ = lean_int_emod(v___x_21_, v_range_20_);
return v___x_22_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__8(void){
_start:
{
lean_object* v_range_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_range_23_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__5, &l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5);
v___x_24_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__7, &l_Std_Time_instInhabitedPlainDateTime_default___closed__7_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__7);
v___x_25_ = lean_int_add(v___x_24_, v_range_23_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__9(void){
_start:
{
lean_object* v_range_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_range_26_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__5, &l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5);
v___x_27_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__8, &l_Std_Time_instInhabitedPlainDateTime_default___closed__8_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__8);
v___x_28_ = lean_int_emod(v___x_27_, v_range_26_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__10(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_30_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__9, &l_Std_Time_instInhabitedPlainDateTime_default___closed__9_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__9);
v___x_31_ = lean_int_add(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(30u);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__12(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_35_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_36_ = lean_int_add(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__13(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_38_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__12, &l_Std_Time_instInhabitedPlainDateTime_default___closed__12_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__12);
v___x_39_ = lean_int_sub(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_range_42_; 
v___x_40_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_41_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__13, &l_Std_Time_instInhabitedPlainDateTime_default___closed__13_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__13);
v_range_42_ = lean_int_add(v___x_41_, v___x_40_);
return v_range_42_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__15(void){
_start:
{
lean_object* v_range_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_range_43_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__14, &l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14);
v___x_44_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__6, &l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6);
v___x_45_ = lean_int_emod(v___x_44_, v_range_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__16(void){
_start:
{
lean_object* v_range_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_range_46_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__14, &l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14);
v___x_47_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__15, &l_Std_Time_instInhabitedPlainDateTime_default___closed__15_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__15);
v___x_48_ = lean_int_add(v___x_47_, v_range_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__17(void){
_start:
{
lean_object* v_range_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_range_49_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__14, &l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14);
v___x_50_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__16, &l_Std_Time_instInhabitedPlainDateTime_default___closed__16_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__16);
v___x_51_ = lean_int_emod(v___x_50_, v_range_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__18(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_53_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__17, &l_Std_Time_instInhabitedPlainDateTime_default___closed__17_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__17);
v___x_54_ = lean_int_add(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__19(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__18, &l_Std_Time_instInhabitedPlainDateTime_default___closed__18_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__18);
v___x_56_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__10, &l_Std_Time_instInhabitedPlainDateTime_default___closed__10_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__10);
v___x_57_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_58_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
lean_ctor_set(v___x_58_, 2, v___x_55_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__20(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(23u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__21(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__20, &l_Std_Time_instInhabitedPlainDateTime_default___closed__20_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__20);
v___x_62_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_63_ = lean_int_add(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__22(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_65_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__21, &l_Std_Time_instInhabitedPlainDateTime_default___closed__21_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__21);
v___x_66_ = lean_int_sub(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_range_69_; 
v___x_67_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_68_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__22, &l_Std_Time_instInhabitedPlainDateTime_default___closed__22_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__22);
v_range_69_ = lean_int_add(v___x_68_, v___x_67_);
return v_range_69_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_71_ = lean_int_sub(v___x_70_, v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__25(void){
_start:
{
lean_object* v_range_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_range_72_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__23, &l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23);
v___x_73_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__24, &l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24);
v___x_74_ = lean_int_emod(v___x_73_, v_range_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__26(void){
_start:
{
lean_object* v_range_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_range_75_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__23, &l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23);
v___x_76_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__25, &l_Std_Time_instInhabitedPlainDateTime_default___closed__25_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__25);
v___x_77_ = lean_int_add(v___x_76_, v_range_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__27(void){
_start:
{
lean_object* v_range_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_range_78_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__23, &l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23);
v___x_79_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__26, &l_Std_Time_instInhabitedPlainDateTime_default___closed__26_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__26);
v___x_80_ = lean_int_emod(v___x_79_, v_range_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__28(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_82_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__27, &l_Std_Time_instInhabitedPlainDateTime_default___closed__27_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__27);
v___x_83_ = lean_int_add(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__29(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(59u);
v___x_85_ = lean_nat_to_int(v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__30(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__29, &l_Std_Time_instInhabitedPlainDateTime_default___closed__29_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__29);
v___x_87_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_88_ = lean_int_add(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__31(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_90_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__30, &l_Std_Time_instInhabitedPlainDateTime_default___closed__30_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__30);
v___x_91_ = lean_int_sub(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_range_94_; 
v___x_92_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_93_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__31, &l_Std_Time_instInhabitedPlainDateTime_default___closed__31_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__31);
v_range_94_ = lean_int_add(v___x_93_, v___x_92_);
return v_range_94_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__33(void){
_start:
{
lean_object* v_range_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_range_95_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__32, &l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32);
v___x_96_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__24, &l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24);
v___x_97_ = lean_int_emod(v___x_96_, v_range_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__34(void){
_start:
{
lean_object* v_range_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_range_98_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__32, &l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32);
v___x_99_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__33, &l_Std_Time_instInhabitedPlainDateTime_default___closed__33_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__33);
v___x_100_ = lean_int_add(v___x_99_, v_range_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__35(void){
_start:
{
lean_object* v_range_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_range_101_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__32, &l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32);
v___x_102_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__34, &l_Std_Time_instInhabitedPlainDateTime_default___closed__34_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__34);
v___x_103_ = lean_int_emod(v___x_102_, v_range_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__36(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_105_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__35, &l_Std_Time_instInhabitedPlainDateTime_default___closed__35_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__35);
v___x_106_ = lean_int_add(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__37(void){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = 1;
v___x_109_ = l_Std_Time_Second_instOfNatOrdinal(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__38(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_111_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__37, &l_Std_Time_instInhabitedPlainDateTime_default___closed__37_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__37);
v___x_112_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__36, &l_Std_Time_instInhabitedPlainDateTime_default___closed__36_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__36);
v___x_113_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__28, &l_Std_Time_instInhabitedPlainDateTime_default___closed__28_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__28);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
lean_ctor_set(v___x_114_, 3, v___x_110_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__39(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__38, &l_Std_Time_instInhabitedPlainDateTime_default___closed__38_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__38);
v___x_116_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__19, &l_Std_Time_instInhabitedPlainDateTime_default___closed__19_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__19);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime_default(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__39, &l_Std_Time_instInhabitedPlainDateTime_default___closed__39_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__39);
return v___x_118_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDateTime(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Time_instInhabitedPlainDateTime_default;
return v___x_119_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDateTime_decEq(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_date_122_; lean_object* v_time_123_; lean_object* v_date_124_; lean_object* v_time_125_; uint8_t v___x_126_; 
v_date_122_ = lean_ctor_get(v_x_120_, 0);
v_time_123_ = lean_ctor_get(v_x_120_, 1);
v_date_124_ = lean_ctor_get(v_x_121_, 0);
v_time_125_ = lean_ctor_get(v_x_121_, 1);
v___x_126_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_date_122_, v_date_124_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_time_123_, v_time_125_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDateTime_decEq___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_128_, v_x_129_);
lean_dec_ref(v_x_129_);
lean_dec_ref(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDateTime(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_132_, v_x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDateTime___boxed(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Std_Time_instDecidableEqPlainDateTime(v_x_135_, v_x_136_);
lean_dec_ref(v_x_136_);
lean_dec_ref(v_x_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(8u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0));
v___x_162_ = lean_string_length(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13, &l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once, _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13);
v___x_164_ = lean_nat_to_int(v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg(lean_object* v_x_169_){
_start:
{
lean_object* v_date_170_; lean_object* v_time_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_203_; 
v_date_170_ = lean_ctor_get(v_x_169_, 0);
v_time_171_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_203_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_203_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_time_171_);
lean_inc(v_date_170_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_203_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_175_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5));
v___x_176_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6));
v___x_177_ = lean_obj_once(&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7, &l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7);
v___x_178_ = l_Std_Time_instReprPlainDate_repr___redArg(v_date_170_);
lean_dec_ref(v_date_170_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 4);
lean_ctor_set(v___x_173_, 1, v___x_178_);
lean_ctor_set(v___x_173_, 0, v___x_177_);
v___x_180_ = v___x_173_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_202_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_176_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9));
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_box(1);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11));
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_175_);
v___x_191_ = l_Std_Time_instReprPlainTime_repr___redArg(v_time_171_);
lean_dec_ref(v_time_171_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_177_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_181_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_obj_once(&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14, &l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14);
v___x_196_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15));
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_194_);
v___x_198_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16));
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_195_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*1, v___x_181_);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr(lean_object* v_x_204_, lean_object* v_prec_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_Time_instReprPlainDateTime_repr___redArg(v_x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr___boxed(lean_object* v_x_207_, lean_object* v_prec_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_Time_instReprPlainDateTime_repr(v_x_207_, v_prec_208_);
lean_dec(v_prec_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__0(lean_object* v_x_212_){
_start:
{
lean_object* v_date_213_; 
v_date_213_ = lean_ctor_get(v_x_212_, 0);
lean_inc_ref(v_date_213_);
return v_date_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__0___boxed(lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Time_instOrdPlainDateTime___lam__0(v_x_214_);
lean_dec_ref(v_x_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__1(lean_object* v_x_216_){
_start:
{
lean_object* v_time_217_; 
v_time_217_ = lean_ctor_get(v_x_216_, 1);
lean_inc_ref(v_time_217_);
return v_time_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__1___boxed(lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Time_instOrdPlainDateTime___lam__1(v_x_218_);
lean_dec_ref(v_x_218_);
return v_res_219_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime___closed__2(void){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___f_222_ = ((lean_object*)(l_Std_Time_instOrdPlainDateTime___closed__0));
v___x_223_ = l_Std_Time_instOrdPlainDate;
v___x_224_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, lean_box(0));
lean_closure_set(v___x_224_, 2, v___x_223_);
lean_closure_set(v___x_224_, 3, v___f_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime___closed__3(void){
_start:
{
lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___f_225_ = ((lean_object*)(l_Std_Time_instOrdPlainDateTime___closed__1));
v___x_226_ = l_Std_Time_instOrdPlainTime;
v___x_227_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_227_, 0, lean_box(0));
lean_closure_set(v___x_227_, 1, lean_box(0));
lean_closure_set(v___x_227_, 2, v___x_226_);
lean_closure_set(v___x_227_, 3, v___f_225_);
return v___x_227_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime___closed__4(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l_Std_Time_instOrdPlainDateTime___closed__3, &l_Std_Time_instOrdPlainDateTime___closed__3_once, _init_l_Std_Time_instOrdPlainDateTime___closed__3);
v___x_229_ = lean_obj_once(&l_Std_Time_instOrdPlainDateTime___closed__2, &l_Std_Time_instOrdPlainDateTime___closed__2_once, _init_l_Std_Time_instOrdPlainDateTime___closed__2);
v___x_230_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_230_, 0, lean_box(0));
lean_closure_set(v___x_230_, 1, lean_box(0));
lean_closure_set(v___x_230_, 2, v___x_229_);
lean_closure_set(v___x_230_, 3, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime(void){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&l_Std_Time_instOrdPlainDateTime___closed__4, &l_Std_Time_instOrdPlainDateTime___closed__4_once, _init_l_Std_Time_instOrdPlainDateTime___closed__4);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__1(lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Rat_ofInt(v_a_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(86400u);
v___x_235_ = lean_nat_to_int(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toWallTime___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1000000000u);
v___x_237_ = lean_nat_to_int(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object* v_dt_238_){
_start:
{
lean_object* v_time_239_; lean_object* v_date_240_; lean_object* v_nanosecond_241_; lean_object* v_days_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_nanos_249_; lean_object* v___x_250_; 
v_time_239_ = lean_ctor_get(v_dt_238_, 1);
lean_inc_ref(v_time_239_);
v_date_240_ = lean_ctor_get(v_dt_238_, 0);
lean_inc_ref(v_date_240_);
lean_dec_ref(v_dt_238_);
v_nanosecond_241_ = lean_ctor_get(v_time_239_, 3);
lean_inc(v_nanosecond_241_);
v_days_242_ = l_Std_Time_PlainDate_toEpochDay(v_date_240_);
v___x_243_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_244_ = lean_int_mul(v_days_242_, v___x_243_);
lean_dec(v_days_242_);
v___x_245_ = l_Std_Time_PlainTime_toSeconds(v_time_239_);
lean_dec_ref(v_time_239_);
v___x_246_ = lean_int_add(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_248_ = lean_int_mul(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
v_nanos_249_ = lean_int_add(v___x_248_, v_nanosecond_241_);
lean_dec(v_nanosecond_241_);
lean_dec(v___x_248_);
v___x_250_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_249_);
lean_dec(v_nanos_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__0(lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_nat_to_int(v_a_251_);
v___x_253_ = l_Rat_ofInt(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_cstr_to_nat("86400000000000");
v___x_255_ = lean_nat_to_int(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object* v_stamp_256_){
_start:
{
lean_object* v_second_257_; lean_object* v_nano_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_272_; 
v_second_257_ = lean_ctor_get(v_stamp_256_, 0);
v_nano_258_ = lean_ctor_get(v_stamp_256_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_stamp_256_);
if (v_isSharedCheck_272_ == 0)
{
v___x_260_ = v_stamp_256_;
v_isShared_261_ = v_isSharedCheck_272_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_nano_258_);
lean_inc(v_second_257_);
lean_dec(v_stamp_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_272_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_nanos_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_262_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_263_ = lean_int_mul(v_second_257_, v___x_262_);
lean_dec(v_second_257_);
v_nanos_264_ = lean_int_add(v___x_263_, v_nano_258_);
lean_dec(v_nano_258_);
lean_dec(v___x_263_);
v___x_265_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__0, &l_Std_Time_PlainDateTime_ofWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0);
v___x_266_ = lean_int_ediv(v_nanos_264_, v___x_265_);
v___x_267_ = l_Std_Time_PlainDate_ofEpochDay(v___x_266_);
lean_dec(v___x_266_);
v___x_268_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_264_);
lean_dec(v_nanos_264_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_268_);
lean_ctor_set(v___x_260_, 0, v___x_267_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object* v_pdt_273_){
_start:
{
lean_object* v_date_274_; lean_object* v___x_275_; 
v_date_274_ = lean_ctor_get(v_pdt_273_, 0);
lean_inc_ref(v_date_274_);
lean_dec_ref(v_pdt_273_);
v___x_275_ = l_Std_Time_PlainDate_toEpochDay(v_date_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object* v_days_276_, lean_object* v_time_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = l_Std_Time_PlainDate_ofEpochDay(v_days_276_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_time_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object* v_days_280_, lean_object* v_time_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_280_, v_time_281_);
lean_dec(v_days_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_283_, uint8_t v_desiredWeekday_284_){
_start:
{
lean_object* v_date_285_; lean_object* v_time_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_date_285_ = lean_ctor_get(v_dt_283_, 0);
v_time_286_ = lean_ctor_get(v_dt_283_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_dt_283_);
if (v_isSharedCheck_294_ == 0)
{
v___x_288_ = v_dt_283_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_time_286_);
lean_inc(v_date_285_);
lean_dec(v_dt_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = l_Std_Time_PlainDate_withWeekday(v_date_285_, v_desiredWeekday_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_time_286_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_295_, lean_object* v_desiredWeekday_296_){
_start:
{
uint8_t v_desiredWeekday_boxed_297_; lean_object* v_res_298_; 
v_desiredWeekday_boxed_297_ = lean_unbox(v_desiredWeekday_296_);
v_res_298_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_295_, v_desiredWeekday_boxed_297_);
return v_res_298_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withDaysClip___closed__0(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(4u);
v___x_300_ = lean_nat_to_int(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withDaysClip___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(100u);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withDaysClip___closed__2(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(400u);
v___x_304_ = lean_nat_to_int(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_305_, lean_object* v_days_306_){
_start:
{
lean_object* v_date_307_; lean_object* v_time_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_345_; 
v_date_307_ = lean_ctor_get(v_dt_305_, 0);
v_time_308_ = lean_ctor_get(v_dt_305_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_dt_305_);
if (v_isSharedCheck_345_ == 0)
{
v___x_310_ = v_dt_305_;
v_isShared_311_ = v_isSharedCheck_345_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_time_308_);
lean_inc(v_date_307_);
lean_dec(v_dt_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_345_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_year_312_; lean_object* v_month_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_343_; 
v_year_312_ = lean_ctor_get(v_date_307_, 0);
v_month_313_ = lean_ctor_get(v_date_307_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_date_307_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_date_307_, 2);
lean_dec(v_unused_344_);
v___x_315_ = v_date_307_;
v_isShared_316_ = v_isSharedCheck_343_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_month_313_);
lean_inc(v_year_312_);
lean_dec(v_date_307_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_343_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
uint8_t v___y_318_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__0, &l_Std_Time_PlainDateTime_withDaysClip___closed__0_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__0);
v___x_334_ = lean_int_mod(v_year_312_, v___x_333_);
v___x_335_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_336_ = lean_int_dec_eq(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
if (v___x_336_ == 0)
{
v___y_318_ = v___x_336_;
goto v___jp_317_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__1, &l_Std_Time_PlainDateTime_withDaysClip___closed__1_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__1);
v___x_338_ = lean_int_mod(v_year_312_, v___x_337_);
v___x_339_ = lean_int_dec_eq(v___x_338_, v___x_335_);
lean_dec(v___x_338_);
if (v___x_339_ == 0)
{
v___y_318_ = v___x_336_;
goto v___jp_317_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__2, &l_Std_Time_PlainDateTime_withDaysClip___closed__2_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__2);
v___x_341_ = lean_int_mod(v_year_312_, v___x_340_);
v___x_342_ = lean_int_dec_eq(v___x_341_, v___x_335_);
lean_dec(v___x_341_);
v___y_318_ = v___x_342_;
goto v___jp_317_;
}
}
v___jp_317_:
{
lean_object* v_max_319_; uint8_t v___x_320_; 
v_max_319_ = l_Std_Time_Month_Ordinal_days(v___y_318_, v_month_313_);
v___x_320_ = lean_int_dec_lt(v_max_319_, v_days_306_);
if (v___x_320_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_max_319_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 2, v_days_306_);
v___x_322_ = v___x_315_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_year_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_month_313_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_days_306_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_322_);
v___x_324_ = v___x_310_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_time_308_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v_days_306_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 2, v_max_319_);
v___x_328_ = v___x_315_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_year_312_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_month_313_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_max_319_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_328_);
v___x_330_ = v___x_310_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_time_308_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_346_, lean_object* v_days_347_){
_start:
{
lean_object* v_date_348_; lean_object* v_time_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_359_; 
v_date_348_ = lean_ctor_get(v_dt_346_, 0);
v_time_349_ = lean_ctor_get(v_dt_346_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_dt_346_);
if (v_isSharedCheck_359_ == 0)
{
v___x_351_ = v_dt_346_;
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_time_349_);
lean_inc(v_date_348_);
lean_dec(v_dt_346_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_year_353_; lean_object* v_month_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v_year_353_ = lean_ctor_get(v_date_348_, 0);
lean_inc(v_year_353_);
v_month_354_ = lean_ctor_get(v_date_348_, 1);
lean_inc(v_month_354_);
lean_dec_ref(v_date_348_);
v___x_355_ = l_Std_Time_PlainDate_rollOver(v_year_353_, v_month_354_, v_days_347_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_355_);
v___x_357_ = v___x_351_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_time_349_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_360_, lean_object* v_days_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_360_, v_days_361_);
lean_dec(v_days_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_363_, lean_object* v_month_364_){
_start:
{
lean_object* v_date_365_; lean_object* v_time_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_403_; 
v_date_365_ = lean_ctor_get(v_dt_363_, 0);
v_time_366_ = lean_ctor_get(v_dt_363_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_dt_363_);
if (v_isSharedCheck_403_ == 0)
{
v___x_368_ = v_dt_363_;
v_isShared_369_ = v_isSharedCheck_403_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_time_366_);
lean_inc(v_date_365_);
lean_dec(v_dt_363_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_403_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_year_370_; lean_object* v_day_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_401_; 
v_year_370_ = lean_ctor_get(v_date_365_, 0);
v_day_371_ = lean_ctor_get(v_date_365_, 2);
v_isSharedCheck_401_ = !lean_is_exclusive(v_date_365_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_date_365_, 1);
lean_dec(v_unused_402_);
v___x_373_ = v_date_365_;
v_isShared_374_ = v_isSharedCheck_401_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_day_371_);
lean_inc(v_year_370_);
lean_dec(v_date_365_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_401_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
uint8_t v___y_376_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__0, &l_Std_Time_PlainDateTime_withDaysClip___closed__0_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__0);
v___x_392_ = lean_int_mod(v_year_370_, v___x_391_);
v___x_393_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_394_ = lean_int_dec_eq(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
v___y_376_ = v___x_394_;
goto v___jp_375_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__1, &l_Std_Time_PlainDateTime_withDaysClip___closed__1_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__1);
v___x_396_ = lean_int_mod(v_year_370_, v___x_395_);
v___x_397_ = lean_int_dec_eq(v___x_396_, v___x_393_);
lean_dec(v___x_396_);
if (v___x_397_ == 0)
{
v___y_376_ = v___x_394_;
goto v___jp_375_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__2, &l_Std_Time_PlainDateTime_withDaysClip___closed__2_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__2);
v___x_399_ = lean_int_mod(v_year_370_, v___x_398_);
v___x_400_ = lean_int_dec_eq(v___x_399_, v___x_393_);
lean_dec(v___x_399_);
v___y_376_ = v___x_400_;
goto v___jp_375_;
}
}
v___jp_375_:
{
lean_object* v_max_377_; uint8_t v___x_378_; 
v_max_377_ = l_Std_Time_Month_Ordinal_days(v___y_376_, v_month_364_);
v___x_378_ = lean_int_dec_lt(v_max_377_, v_day_371_);
if (v___x_378_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v_max_377_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 1, v_month_364_);
v___x_380_ = v___x_373_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_year_370_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_month_364_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_day_371_);
v___x_380_ = v_reuseFailAlloc_384_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_380_);
v___x_382_ = v___x_368_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_time_366_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec(v_day_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 2, v_max_377_);
lean_ctor_set(v___x_373_, 1, v_month_364_);
v___x_386_ = v___x_373_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_year_370_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_month_364_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_max_377_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_386_);
v___x_388_ = v___x_368_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_time_366_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_404_, lean_object* v_month_405_){
_start:
{
lean_object* v_date_406_; lean_object* v_time_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_417_; 
v_date_406_ = lean_ctor_get(v_dt_404_, 0);
v_time_407_ = lean_ctor_get(v_dt_404_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_dt_404_);
if (v_isSharedCheck_417_ == 0)
{
v___x_409_ = v_dt_404_;
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_time_407_);
lean_inc(v_date_406_);
lean_dec(v_dt_404_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_year_411_; lean_object* v_day_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_year_411_ = lean_ctor_get(v_date_406_, 0);
lean_inc(v_year_411_);
v_day_412_ = lean_ctor_get(v_date_406_, 2);
lean_inc(v_day_412_);
lean_dec_ref(v_date_406_);
v___x_413_ = l_Std_Time_PlainDate_rollOver(v_year_411_, v_month_405_, v_day_412_);
lean_dec(v_day_412_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_413_);
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_time_407_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_418_, lean_object* v_year_419_){
_start:
{
lean_object* v_date_420_; lean_object* v_time_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_458_; 
v_date_420_ = lean_ctor_get(v_dt_418_, 0);
v_time_421_ = lean_ctor_get(v_dt_418_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_dt_418_);
if (v_isSharedCheck_458_ == 0)
{
v___x_423_ = v_dt_418_;
v_isShared_424_ = v_isSharedCheck_458_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_time_421_);
lean_inc(v_date_420_);
lean_dec(v_dt_418_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_458_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_month_425_; lean_object* v_day_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_456_; 
v_month_425_ = lean_ctor_get(v_date_420_, 1);
v_day_426_ = lean_ctor_get(v_date_420_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_date_420_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_date_420_, 0);
lean_dec(v_unused_457_);
v___x_428_ = v_date_420_;
v_isShared_429_ = v_isSharedCheck_456_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_day_426_);
lean_inc(v_month_425_);
lean_dec(v_date_420_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_456_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___y_431_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_446_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__0, &l_Std_Time_PlainDateTime_withDaysClip___closed__0_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__0);
v___x_447_ = lean_int_mod(v_year_419_, v___x_446_);
v___x_448_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_449_ = lean_int_dec_eq(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
if (v___x_449_ == 0)
{
v___y_431_ = v___x_449_;
goto v___jp_430_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__1, &l_Std_Time_PlainDateTime_withDaysClip___closed__1_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__1);
v___x_451_ = lean_int_mod(v_year_419_, v___x_450_);
v___x_452_ = lean_int_dec_eq(v___x_451_, v___x_448_);
lean_dec(v___x_451_);
if (v___x_452_ == 0)
{
v___y_431_ = v___x_449_;
goto v___jp_430_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__2, &l_Std_Time_PlainDateTime_withDaysClip___closed__2_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__2);
v___x_454_ = lean_int_mod(v_year_419_, v___x_453_);
v___x_455_ = lean_int_dec_eq(v___x_454_, v___x_448_);
lean_dec(v___x_454_);
v___y_431_ = v___x_455_;
goto v___jp_430_;
}
}
v___jp_430_:
{
lean_object* v_max_432_; uint8_t v___x_433_; 
v_max_432_ = l_Std_Time_Month_Ordinal_days(v___y_431_, v_month_425_);
v___x_433_ = lean_int_dec_lt(v_max_432_, v_day_426_);
if (v___x_433_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_max_432_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_year_419_);
v___x_435_ = v___x_428_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_year_419_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_month_425_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_day_426_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_435_);
v___x_437_ = v___x_423_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_time_421_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v_day_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 2, v_max_432_);
lean_ctor_set(v___x_428_, 0, v_year_419_);
v___x_441_ = v___x_428_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_year_419_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_month_425_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_max_432_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_441_);
v___x_443_ = v___x_423_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_time_421_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_459_, lean_object* v_year_460_){
_start:
{
lean_object* v_date_461_; lean_object* v_time_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
v_date_461_ = lean_ctor_get(v_dt_459_, 0);
v_time_462_ = lean_ctor_get(v_dt_459_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_dt_459_);
if (v_isSharedCheck_472_ == 0)
{
v___x_464_ = v_dt_459_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_time_462_);
lean_inc(v_date_461_);
lean_dec(v_dt_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_month_466_; lean_object* v_day_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v_month_466_ = lean_ctor_get(v_date_461_, 1);
lean_inc(v_month_466_);
v_day_467_ = lean_ctor_get(v_date_461_, 2);
lean_inc(v_day_467_);
lean_dec_ref(v_date_461_);
v___x_468_ = l_Std_Time_PlainDate_rollOver(v_year_460_, v_month_466_, v_day_467_);
lean_dec(v_day_467_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_468_);
v___x_470_ = v___x_464_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_time_462_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_473_, lean_object* v_hour_474_){
_start:
{
lean_object* v_time_475_; lean_object* v_date_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_494_; 
v_time_475_ = lean_ctor_get(v_dt_473_, 1);
v_date_476_ = lean_ctor_get(v_dt_473_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_dt_473_);
if (v_isSharedCheck_494_ == 0)
{
v___x_478_ = v_dt_473_;
v_isShared_479_ = v_isSharedCheck_494_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_time_475_);
lean_inc(v_date_476_);
lean_dec(v_dt_473_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_494_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_minute_480_; lean_object* v_second_481_; lean_object* v_nanosecond_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_492_; 
v_minute_480_ = lean_ctor_get(v_time_475_, 1);
v_second_481_ = lean_ctor_get(v_time_475_, 2);
v_nanosecond_482_ = lean_ctor_get(v_time_475_, 3);
v_isSharedCheck_492_ = !lean_is_exclusive(v_time_475_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_time_475_, 0);
lean_dec(v_unused_493_);
v___x_484_ = v_time_475_;
v_isShared_485_ = v_isSharedCheck_492_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_nanosecond_482_);
lean_inc(v_second_481_);
lean_inc(v_minute_480_);
lean_dec(v_time_475_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_492_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_hour_474_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_hour_474_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_minute_480_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_second_481_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_nanosecond_482_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_487_);
v___x_489_ = v___x_478_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_date_476_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_495_, lean_object* v_minute_496_){
_start:
{
lean_object* v_time_497_; lean_object* v_date_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_516_; 
v_time_497_ = lean_ctor_get(v_dt_495_, 1);
v_date_498_ = lean_ctor_get(v_dt_495_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_dt_495_);
if (v_isSharedCheck_516_ == 0)
{
v___x_500_ = v_dt_495_;
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_time_497_);
lean_inc(v_date_498_);
lean_dec(v_dt_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_hour_502_; lean_object* v_second_503_; lean_object* v_nanosecond_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_514_; 
v_hour_502_ = lean_ctor_get(v_time_497_, 0);
v_second_503_ = lean_ctor_get(v_time_497_, 2);
v_nanosecond_504_ = lean_ctor_get(v_time_497_, 3);
v_isSharedCheck_514_ = !lean_is_exclusive(v_time_497_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_time_497_, 1);
lean_dec(v_unused_515_);
v___x_506_ = v_time_497_;
v_isShared_507_ = v_isSharedCheck_514_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_nanosecond_504_);
lean_inc(v_second_503_);
lean_inc(v_hour_502_);
lean_dec(v_time_497_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_514_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_minute_496_);
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_hour_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_minute_496_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_second_503_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_nanosecond_504_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_509_);
v___x_511_ = v___x_500_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_date_498_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_517_, lean_object* v_second_518_){
_start:
{
lean_object* v_time_519_; lean_object* v_date_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_538_; 
v_time_519_ = lean_ctor_get(v_dt_517_, 1);
v_date_520_ = lean_ctor_get(v_dt_517_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_dt_517_);
if (v_isSharedCheck_538_ == 0)
{
v___x_522_ = v_dt_517_;
v_isShared_523_ = v_isSharedCheck_538_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_time_519_);
lean_inc(v_date_520_);
lean_dec(v_dt_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_538_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_hour_524_; lean_object* v_minute_525_; lean_object* v_nanosecond_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_536_; 
v_hour_524_ = lean_ctor_get(v_time_519_, 0);
v_minute_525_ = lean_ctor_get(v_time_519_, 1);
v_nanosecond_526_ = lean_ctor_get(v_time_519_, 3);
v_isSharedCheck_536_ = !lean_is_exclusive(v_time_519_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_time_519_, 2);
lean_dec(v_unused_537_);
v___x_528_ = v_time_519_;
v_isShared_529_ = v_isSharedCheck_536_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_nanosecond_526_);
lean_inc(v_minute_525_);
lean_inc(v_hour_524_);
lean_dec(v_time_519_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_536_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 2, v_second_518_);
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_hour_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_minute_525_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_second_518_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_nanosecond_526_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_531_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_date_520_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1000u);
v___x_540_ = lean_nat_to_int(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(1000000u);
v___x_542_ = lean_nat_to_int(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_543_, lean_object* v_millis_544_){
_start:
{
lean_object* v_time_545_; lean_object* v_date_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_569_; 
v_time_545_ = lean_ctor_get(v_dt_543_, 1);
v_date_546_ = lean_ctor_get(v_dt_543_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_dt_543_);
if (v_isSharedCheck_569_ == 0)
{
v___x_548_ = v_dt_543_;
v_isShared_549_ = v_isSharedCheck_569_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_time_545_);
lean_inc(v_date_546_);
lean_dec(v_dt_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_569_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_hour_550_; lean_object* v_minute_551_; lean_object* v_second_552_; lean_object* v_nanosecond_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_568_; 
v_hour_550_ = lean_ctor_get(v_time_545_, 0);
v_minute_551_ = lean_ctor_get(v_time_545_, 1);
v_second_552_ = lean_ctor_get(v_time_545_, 2);
v_nanosecond_553_ = lean_ctor_get(v_time_545_, 3);
v_isSharedCheck_568_ = !lean_is_exclusive(v_time_545_);
if (v_isSharedCheck_568_ == 0)
{
v___x_555_ = v_time_545_;
v_isShared_556_ = v_isSharedCheck_568_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_nanosecond_553_);
lean_inc(v_second_552_);
lean_inc(v_minute_551_);
lean_inc(v_hour_550_);
lean_dec(v_time_545_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_568_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_557_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_558_ = lean_int_emod(v_nanosecond_553_, v___x_557_);
lean_dec(v_nanosecond_553_);
v___x_559_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_560_ = lean_int_mul(v_millis_544_, v___x_559_);
v___x_561_ = lean_int_add(v___x_560_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_560_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 3, v___x_561_);
v___x_563_ = v___x_555_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_hour_550_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_minute_551_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_second_552_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v___x_561_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_563_);
v___x_565_ = v___x_548_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_date_546_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_570_, lean_object* v_millis_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_570_, v_millis_571_);
lean_dec(v_millis_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_573_, lean_object* v_nano_574_){
_start:
{
lean_object* v_time_575_; lean_object* v_date_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_594_; 
v_time_575_ = lean_ctor_get(v_dt_573_, 1);
v_date_576_ = lean_ctor_get(v_dt_573_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_dt_573_);
if (v_isSharedCheck_594_ == 0)
{
v___x_578_ = v_dt_573_;
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_time_575_);
lean_inc(v_date_576_);
lean_dec(v_dt_573_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_hour_580_; lean_object* v_minute_581_; lean_object* v_second_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_592_; 
v_hour_580_ = lean_ctor_get(v_time_575_, 0);
v_minute_581_ = lean_ctor_get(v_time_575_, 1);
v_second_582_ = lean_ctor_get(v_time_575_, 2);
v_isSharedCheck_592_ = !lean_is_exclusive(v_time_575_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v_time_575_, 3);
lean_dec(v_unused_593_);
v___x_584_ = v_time_575_;
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_second_582_);
lean_inc(v_minute_581_);
lean_inc(v_hour_580_);
lean_dec(v_time_575_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 3, v_nano_574_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_hour_580_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_minute_581_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_second_582_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_nano_574_);
v___x_587_ = v_reuseFailAlloc_591_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___x_587_);
v___x_589_ = v___x_578_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_date_576_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_595_, lean_object* v_days_596_){
_start:
{
lean_object* v_date_597_; lean_object* v_time_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_608_; 
v_date_597_ = lean_ctor_get(v_dt_595_, 0);
v_time_598_ = lean_ctor_get(v_dt_595_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_dt_595_);
if (v_isSharedCheck_608_ == 0)
{
v___x_600_ = v_dt_595_;
v_isShared_601_ = v_isSharedCheck_608_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_time_598_);
lean_inc(v_date_597_);
lean_dec(v_dt_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_608_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_dateDays_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v_dateDays_602_ = l_Std_Time_PlainDate_toEpochDay(v_date_597_);
v___x_603_ = lean_int_add(v_dateDays_602_, v_days_596_);
lean_dec(v_dateDays_602_);
v___x_604_ = l_Std_Time_PlainDate_ofEpochDay(v___x_603_);
lean_dec(v___x_603_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_604_);
v___x_606_ = v___x_600_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_time_598_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_609_, lean_object* v_days_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Time_PlainDateTime_addDays(v_dt_609_, v_days_610_);
lean_dec(v_days_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_612_, lean_object* v_days_613_){
_start:
{
lean_object* v_date_614_; lean_object* v_time_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_626_; 
v_date_614_ = lean_ctor_get(v_dt_612_, 0);
v_time_615_ = lean_ctor_get(v_dt_612_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_dt_612_);
if (v_isSharedCheck_626_ == 0)
{
v___x_617_ = v_dt_612_;
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_time_615_);
lean_inc(v_date_614_);
lean_dec(v_dt_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v_dateDays_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_619_ = lean_int_neg(v_days_613_);
v_dateDays_620_ = l_Std_Time_PlainDate_toEpochDay(v_date_614_);
v___x_621_ = lean_int_add(v_dateDays_620_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v_dateDays_620_);
v___x_622_ = l_Std_Time_PlainDate_ofEpochDay(v___x_621_);
lean_dec(v___x_621_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_622_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_time_615_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_627_, lean_object* v_days_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Time_PlainDateTime_subDays(v_dt_627_, v_days_628_);
lean_dec(v_days_628_);
return v_res_629_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(7u);
v___x_631_ = lean_nat_to_int(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_632_, lean_object* v_weeks_633_){
_start:
{
lean_object* v_date_634_; lean_object* v_time_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
v_date_634_ = lean_ctor_get(v_dt_632_, 0);
v_time_635_ = lean_ctor_get(v_dt_632_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_dt_632_);
if (v_isSharedCheck_647_ == 0)
{
v___x_637_ = v_dt_632_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_time_635_);
lean_inc(v_date_634_);
lean_dec(v_dt_632_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_dateDays_639_; lean_object* v___x_640_; lean_object* v_daysToAdd_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v_dateDays_639_ = l_Std_Time_PlainDate_toEpochDay(v_date_634_);
v___x_640_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_641_ = lean_int_mul(v_weeks_633_, v___x_640_);
v___x_642_ = lean_int_add(v_dateDays_639_, v_daysToAdd_641_);
lean_dec(v_daysToAdd_641_);
lean_dec(v_dateDays_639_);
v___x_643_ = l_Std_Time_PlainDate_ofEpochDay(v___x_642_);
lean_dec(v___x_642_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_643_);
v___x_645_ = v___x_637_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_time_635_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_648_, lean_object* v_weeks_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_648_, v_weeks_649_);
lean_dec(v_weeks_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_651_, lean_object* v_weeks_652_){
_start:
{
lean_object* v_date_653_; lean_object* v_time_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_date_653_ = lean_ctor_get(v_dt_651_, 0);
v_time_654_ = lean_ctor_get(v_dt_651_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_dt_651_);
if (v_isSharedCheck_667_ == 0)
{
v___x_656_ = v_dt_651_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_time_654_);
lean_inc(v_date_653_);
lean_dec(v_dt_651_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v_dateDays_659_; lean_object* v___x_660_; lean_object* v_daysToAdd_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_658_ = lean_int_neg(v_weeks_652_);
v_dateDays_659_ = l_Std_Time_PlainDate_toEpochDay(v_date_653_);
v___x_660_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_661_ = lean_int_mul(v___x_658_, v___x_660_);
lean_dec(v___x_658_);
v___x_662_ = lean_int_add(v_dateDays_659_, v_daysToAdd_661_);
lean_dec(v_daysToAdd_661_);
lean_dec(v_dateDays_659_);
v___x_663_ = l_Std_Time_PlainDate_ofEpochDay(v___x_662_);
lean_dec(v___x_662_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_663_);
v___x_665_ = v___x_656_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_time_654_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_668_, lean_object* v_weeks_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_668_, v_weeks_669_);
lean_dec(v_weeks_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_671_, lean_object* v_months_672_){
_start:
{
lean_object* v_date_673_; lean_object* v_time_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_date_673_ = lean_ctor_get(v_dt_671_, 0);
v_time_674_ = lean_ctor_get(v_dt_671_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_dt_671_);
if (v_isSharedCheck_682_ == 0)
{
v___x_676_ = v_dt_671_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_time_674_);
lean_inc(v_date_673_);
lean_dec(v_dt_671_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Std_Time_PlainDate_addMonthsClip(v_date_673_, v_months_672_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_time_674_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_683_, lean_object* v_months_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_683_, v_months_684_);
lean_dec(v_months_684_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_686_, lean_object* v_months_687_){
_start:
{
lean_object* v_date_688_; lean_object* v_time_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_698_; 
v_date_688_ = lean_ctor_get(v_dt_686_, 0);
v_time_689_ = lean_ctor_get(v_dt_686_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_dt_686_);
if (v_isSharedCheck_698_ == 0)
{
v___x_691_ = v_dt_686_;
v_isShared_692_ = v_isSharedCheck_698_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_time_689_);
lean_inc(v_date_688_);
lean_dec(v_dt_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_698_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = lean_int_neg(v_months_687_);
v___x_694_ = l_Std_Time_PlainDate_addMonthsClip(v_date_688_, v___x_693_);
lean_dec(v___x_693_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_time_689_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_699_, lean_object* v_months_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_699_, v_months_700_);
lean_dec(v_months_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_702_, lean_object* v_months_703_){
_start:
{
lean_object* v_date_704_; lean_object* v_time_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
v_date_704_ = lean_ctor_get(v_dt_702_, 0);
v_time_705_ = lean_ctor_get(v_dt_702_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_dt_702_);
if (v_isSharedCheck_713_ == 0)
{
v___x_707_ = v_dt_702_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_time_705_);
lean_inc(v_date_704_);
lean_dec(v_dt_702_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_704_, v_months_703_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_time_705_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_714_, lean_object* v_months_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_714_, v_months_715_);
lean_dec(v_months_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_717_, lean_object* v_months_718_){
_start:
{
lean_object* v_date_719_; lean_object* v_time_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_729_; 
v_date_719_ = lean_ctor_get(v_dt_717_, 0);
v_time_720_ = lean_ctor_get(v_dt_717_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_dt_717_);
if (v_isSharedCheck_729_ == 0)
{
v___x_722_ = v_dt_717_;
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_time_720_);
lean_inc(v_date_719_);
lean_dec(v_dt_717_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = lean_int_neg(v_months_718_);
v___x_725_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_719_, v___x_724_);
lean_dec(v___x_724_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_time_720_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_730_, lean_object* v_months_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_730_, v_months_731_);
lean_dec(v_months_731_);
return v_res_732_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(12u);
v___x_734_ = lean_nat_to_int(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_735_, lean_object* v_years_736_){
_start:
{
lean_object* v_date_737_; lean_object* v_time_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
v_date_737_ = lean_ctor_get(v_dt_735_, 0);
v_time_738_ = lean_ctor_get(v_dt_735_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_dt_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_740_ = v_dt_735_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_time_738_);
lean_inc(v_date_737_);
lean_dec(v_dt_735_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_742_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_743_ = lean_int_mul(v_years_736_, v___x_742_);
v___x_744_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_737_, v___x_743_);
lean_dec(v___x_743_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_time_738_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_749_, lean_object* v_years_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_749_, v_years_750_);
lean_dec(v_years_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_752_, lean_object* v_years_753_){
_start:
{
lean_object* v_date_754_; lean_object* v_time_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_765_; 
v_date_754_ = lean_ctor_get(v_dt_752_, 0);
v_time_755_ = lean_ctor_get(v_dt_752_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_dt_752_);
if (v_isSharedCheck_765_ == 0)
{
v___x_757_ = v_dt_752_;
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_time_755_);
lean_inc(v_date_754_);
lean_dec(v_dt_752_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_759_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_760_ = lean_int_mul(v_years_753_, v___x_759_);
v___x_761_ = l_Std_Time_PlainDate_addMonthsClip(v_date_754_, v___x_760_);
lean_dec(v___x_760_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_761_);
v___x_763_ = v___x_757_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_time_755_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_766_, lean_object* v_years_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_766_, v_years_767_);
lean_dec(v_years_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_769_, lean_object* v_years_770_){
_start:
{
lean_object* v_date_771_; lean_object* v_time_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v_date_771_ = lean_ctor_get(v_dt_769_, 0);
v_time_772_ = lean_ctor_get(v_dt_769_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_dt_769_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v_dt_769_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_time_772_);
lean_inc(v_date_771_);
lean_dec(v_dt_769_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_776_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_777_ = lean_int_mul(v_years_770_, v___x_776_);
v___x_778_ = lean_int_neg(v___x_777_);
lean_dec(v___x_777_);
v___x_779_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_771_, v___x_778_);
lean_dec(v___x_778_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_779_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_time_772_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_784_, lean_object* v_years_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_784_, v_years_785_);
lean_dec(v_years_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_787_, lean_object* v_years_788_){
_start:
{
lean_object* v_date_789_; lean_object* v_time_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_801_; 
v_date_789_ = lean_ctor_get(v_dt_787_, 0);
v_time_790_ = lean_ctor_get(v_dt_787_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_dt_787_);
if (v_isSharedCheck_801_ == 0)
{
v___x_792_ = v_dt_787_;
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_time_790_);
lean_inc(v_date_789_);
lean_dec(v_dt_787_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_794_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_795_ = lean_int_mul(v_years_788_, v___x_794_);
v___x_796_ = lean_int_neg(v___x_795_);
lean_dec(v___x_795_);
v___x_797_ = l_Std_Time_PlainDate_addMonthsClip(v_date_789_, v___x_796_);
lean_dec(v___x_796_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_time_790_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_802_, lean_object* v_years_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_802_, v_years_803_);
lean_dec(v_years_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_805_, lean_object* v_nanos_806_){
_start:
{
lean_object* v___x_807_; lean_object* v_second_808_; lean_object* v_nano_809_; lean_object* v___x_810_; lean_object* v_second_811_; lean_object* v_nano_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_nanos_815_; lean_object* v___x_816_; lean_object* v_nanos_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_807_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_805_);
v_second_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_second_808_);
v_nano_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc(v_nano_809_);
lean_dec_ref(v___x_807_);
v___x_810_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_806_);
v_second_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_second_811_);
v_nano_812_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_nano_812_);
lean_dec_ref(v___x_810_);
v___x_813_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_814_ = lean_int_mul(v_second_808_, v___x_813_);
lean_dec(v_second_808_);
v_nanos_815_ = lean_int_add(v___x_814_, v_nano_809_);
lean_dec(v_nano_809_);
lean_dec(v___x_814_);
v___x_816_ = lean_int_mul(v_second_811_, v___x_813_);
lean_dec(v_second_811_);
v_nanos_817_ = lean_int_add(v___x_816_, v_nano_812_);
lean_dec(v_nano_812_);
lean_dec(v___x_816_);
v___x_818_ = lean_int_add(v_nanos_815_, v_nanos_817_);
lean_dec(v_nanos_817_);
lean_dec(v_nanos_815_);
v___x_819_ = l_Std_Time_Duration_ofNanoseconds(v___x_818_);
lean_dec(v___x_818_);
v___x_820_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_821_, lean_object* v_nanos_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_821_, v_nanos_822_);
lean_dec(v_nanos_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_824_, lean_object* v_nanos_825_){
_start:
{
lean_object* v___x_826_; lean_object* v_second_827_; lean_object* v_nano_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_second_831_; lean_object* v_nano_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_nanos_835_; lean_object* v___x_836_; lean_object* v_nanos_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_826_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_824_);
v_second_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_second_827_);
v_nano_828_ = lean_ctor_get(v___x_826_, 1);
lean_inc(v_nano_828_);
lean_dec_ref(v___x_826_);
v___x_829_ = lean_int_neg(v_nanos_825_);
v___x_830_ = l_Std_Time_Duration_ofNanoseconds(v___x_829_);
lean_dec(v___x_829_);
v_second_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_second_831_);
v_nano_832_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_nano_832_);
lean_dec_ref(v___x_830_);
v___x_833_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_834_ = lean_int_mul(v_second_827_, v___x_833_);
lean_dec(v_second_827_);
v_nanos_835_ = lean_int_add(v___x_834_, v_nano_828_);
lean_dec(v_nano_828_);
lean_dec(v___x_834_);
v___x_836_ = lean_int_mul(v_second_831_, v___x_833_);
lean_dec(v_second_831_);
v_nanos_837_ = lean_int_add(v___x_836_, v_nano_832_);
lean_dec(v_nano_832_);
lean_dec(v___x_836_);
v___x_838_ = lean_int_add(v_nanos_835_, v_nanos_837_);
lean_dec(v_nanos_837_);
lean_dec(v_nanos_835_);
v___x_839_ = l_Std_Time_Duration_ofNanoseconds(v___x_838_);
lean_dec(v___x_838_);
v___x_840_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_841_, lean_object* v_nanos_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_841_, v_nanos_842_);
lean_dec(v_nanos_842_);
return v_res_843_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_cstr_to_nat("3600000000000");
v___x_845_ = lean_nat_to_int(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_846_, lean_object* v_hours_847_){
_start:
{
lean_object* v___x_848_; lean_object* v_second_849_; lean_object* v_nano_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_second_854_; lean_object* v_nano_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_nanos_858_; lean_object* v___x_859_; lean_object* v_nanos_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_848_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_846_);
v_second_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_second_849_);
v_nano_850_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_nano_850_);
lean_dec_ref(v___x_848_);
v___x_851_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_852_ = lean_int_mul(v_hours_847_, v___x_851_);
v___x_853_ = l_Std_Time_Duration_ofNanoseconds(v___x_852_);
lean_dec(v___x_852_);
v_second_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_second_854_);
v_nano_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_nano_855_);
lean_dec_ref(v___x_853_);
v___x_856_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_857_ = lean_int_mul(v_second_849_, v___x_856_);
lean_dec(v_second_849_);
v_nanos_858_ = lean_int_add(v___x_857_, v_nano_850_);
lean_dec(v_nano_850_);
lean_dec(v___x_857_);
v___x_859_ = lean_int_mul(v_second_854_, v___x_856_);
lean_dec(v_second_854_);
v_nanos_860_ = lean_int_add(v___x_859_, v_nano_855_);
lean_dec(v_nano_855_);
lean_dec(v___x_859_);
v___x_861_ = lean_int_add(v_nanos_858_, v_nanos_860_);
lean_dec(v_nanos_860_);
lean_dec(v_nanos_858_);
v___x_862_ = l_Std_Time_Duration_ofNanoseconds(v___x_861_);
lean_dec(v___x_861_);
v___x_863_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_864_, lean_object* v_hours_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_Time_PlainDateTime_addHours(v_dt_864_, v_hours_865_);
lean_dec(v_hours_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_867_, lean_object* v_hours_868_){
_start:
{
lean_object* v___x_869_; lean_object* v_second_870_; lean_object* v_nano_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_second_876_; lean_object* v_nano_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_nanos_880_; lean_object* v___x_881_; lean_object* v_nanos_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_869_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_867_);
v_second_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_second_870_);
v_nano_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_nano_871_);
lean_dec_ref(v___x_869_);
v___x_872_ = lean_int_neg(v_hours_868_);
v___x_873_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_874_ = lean_int_mul(v___x_872_, v___x_873_);
lean_dec(v___x_872_);
v___x_875_ = l_Std_Time_Duration_ofNanoseconds(v___x_874_);
lean_dec(v___x_874_);
v_second_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_second_876_);
v_nano_877_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_nano_877_);
lean_dec_ref(v___x_875_);
v___x_878_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_879_ = lean_int_mul(v_second_870_, v___x_878_);
lean_dec(v_second_870_);
v_nanos_880_ = lean_int_add(v___x_879_, v_nano_871_);
lean_dec(v_nano_871_);
lean_dec(v___x_879_);
v___x_881_ = lean_int_mul(v_second_876_, v___x_878_);
lean_dec(v_second_876_);
v_nanos_882_ = lean_int_add(v___x_881_, v_nano_877_);
lean_dec(v_nano_877_);
lean_dec(v___x_881_);
v___x_883_ = lean_int_add(v_nanos_880_, v_nanos_882_);
lean_dec(v_nanos_882_);
lean_dec(v_nanos_880_);
v___x_884_ = l_Std_Time_Duration_ofNanoseconds(v___x_883_);
lean_dec(v___x_883_);
v___x_885_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_886_, lean_object* v_hours_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_Time_PlainDateTime_subHours(v_dt_886_, v_hours_887_);
lean_dec(v_hours_887_);
return v_res_888_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_cstr_to_nat("60000000000");
v___x_890_ = lean_nat_to_int(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_891_, lean_object* v_minutes_892_){
_start:
{
lean_object* v___x_893_; lean_object* v_second_894_; lean_object* v_nano_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_second_899_; lean_object* v_nano_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_nanos_903_; lean_object* v___x_904_; lean_object* v_nanos_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_893_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_891_);
v_second_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_second_894_);
v_nano_895_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_nano_895_);
lean_dec_ref(v___x_893_);
v___x_896_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_897_ = lean_int_mul(v_minutes_892_, v___x_896_);
v___x_898_ = l_Std_Time_Duration_ofNanoseconds(v___x_897_);
lean_dec(v___x_897_);
v_second_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_second_899_);
v_nano_900_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_nano_900_);
lean_dec_ref(v___x_898_);
v___x_901_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_902_ = lean_int_mul(v_second_894_, v___x_901_);
lean_dec(v_second_894_);
v_nanos_903_ = lean_int_add(v___x_902_, v_nano_895_);
lean_dec(v_nano_895_);
lean_dec(v___x_902_);
v___x_904_ = lean_int_mul(v_second_899_, v___x_901_);
lean_dec(v_second_899_);
v_nanos_905_ = lean_int_add(v___x_904_, v_nano_900_);
lean_dec(v_nano_900_);
lean_dec(v___x_904_);
v___x_906_ = lean_int_add(v_nanos_903_, v_nanos_905_);
lean_dec(v_nanos_905_);
lean_dec(v_nanos_903_);
v___x_907_ = l_Std_Time_Duration_ofNanoseconds(v___x_906_);
lean_dec(v___x_906_);
v___x_908_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_909_, lean_object* v_minutes_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_909_, v_minutes_910_);
lean_dec(v_minutes_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_912_, lean_object* v_minutes_913_){
_start:
{
lean_object* v___x_914_; lean_object* v_second_915_; lean_object* v_nano_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_second_921_; lean_object* v_nano_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_nanos_925_; lean_object* v___x_926_; lean_object* v_nanos_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_914_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_912_);
v_second_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_second_915_);
v_nano_916_ = lean_ctor_get(v___x_914_, 1);
lean_inc(v_nano_916_);
lean_dec_ref(v___x_914_);
v___x_917_ = lean_int_neg(v_minutes_913_);
v___x_918_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_919_ = lean_int_mul(v___x_917_, v___x_918_);
lean_dec(v___x_917_);
v___x_920_ = l_Std_Time_Duration_ofNanoseconds(v___x_919_);
lean_dec(v___x_919_);
v_second_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_second_921_);
v_nano_922_ = lean_ctor_get(v___x_920_, 1);
lean_inc(v_nano_922_);
lean_dec_ref(v___x_920_);
v___x_923_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_924_ = lean_int_mul(v_second_915_, v___x_923_);
lean_dec(v_second_915_);
v_nanos_925_ = lean_int_add(v___x_924_, v_nano_916_);
lean_dec(v_nano_916_);
lean_dec(v___x_924_);
v___x_926_ = lean_int_mul(v_second_921_, v___x_923_);
lean_dec(v_second_921_);
v_nanos_927_ = lean_int_add(v___x_926_, v_nano_922_);
lean_dec(v_nano_922_);
lean_dec(v___x_926_);
v___x_928_ = lean_int_add(v_nanos_925_, v_nanos_927_);
lean_dec(v_nanos_927_);
lean_dec(v_nanos_925_);
v___x_929_ = l_Std_Time_Duration_ofNanoseconds(v___x_928_);
lean_dec(v___x_928_);
v___x_930_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_931_, lean_object* v_minutes_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_931_, v_minutes_932_);
lean_dec(v_minutes_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_934_, lean_object* v_seconds_935_){
_start:
{
lean_object* v___x_936_; lean_object* v_second_937_; lean_object* v_nano_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_second_942_; lean_object* v_nano_943_; lean_object* v___x_944_; lean_object* v_nanos_945_; lean_object* v___x_946_; lean_object* v_nanos_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_936_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_934_);
v_second_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_second_937_);
v_nano_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc(v_nano_938_);
lean_dec_ref(v___x_936_);
v___x_939_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_940_ = lean_int_mul(v_seconds_935_, v___x_939_);
v___x_941_ = l_Std_Time_Duration_ofNanoseconds(v___x_940_);
lean_dec(v___x_940_);
v_second_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_second_942_);
v_nano_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_nano_943_);
lean_dec_ref(v___x_941_);
v___x_944_ = lean_int_mul(v_second_937_, v___x_939_);
lean_dec(v_second_937_);
v_nanos_945_ = lean_int_add(v___x_944_, v_nano_938_);
lean_dec(v_nano_938_);
lean_dec(v___x_944_);
v___x_946_ = lean_int_mul(v_second_942_, v___x_939_);
lean_dec(v_second_942_);
v_nanos_947_ = lean_int_add(v___x_946_, v_nano_943_);
lean_dec(v_nano_943_);
lean_dec(v___x_946_);
v___x_948_ = lean_int_add(v_nanos_945_, v_nanos_947_);
lean_dec(v_nanos_947_);
lean_dec(v_nanos_945_);
v___x_949_ = l_Std_Time_Duration_ofNanoseconds(v___x_948_);
lean_dec(v___x_948_);
v___x_950_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_951_, lean_object* v_seconds_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_951_, v_seconds_952_);
lean_dec(v_seconds_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_954_, lean_object* v_seconds_955_){
_start:
{
lean_object* v___x_956_; lean_object* v_second_957_; lean_object* v_nano_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_second_963_; lean_object* v_nano_964_; lean_object* v___x_965_; lean_object* v_nanos_966_; lean_object* v___x_967_; lean_object* v_nanos_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_956_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_954_);
v_second_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_second_957_);
v_nano_958_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_nano_958_);
lean_dec_ref(v___x_956_);
v___x_959_ = lean_int_neg(v_seconds_955_);
v___x_960_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_961_ = lean_int_mul(v___x_959_, v___x_960_);
lean_dec(v___x_959_);
v___x_962_ = l_Std_Time_Duration_ofNanoseconds(v___x_961_);
lean_dec(v___x_961_);
v_second_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_second_963_);
v_nano_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_nano_964_);
lean_dec_ref(v___x_962_);
v___x_965_ = lean_int_mul(v_second_957_, v___x_960_);
lean_dec(v_second_957_);
v_nanos_966_ = lean_int_add(v___x_965_, v_nano_958_);
lean_dec(v_nano_958_);
lean_dec(v___x_965_);
v___x_967_ = lean_int_mul(v_second_963_, v___x_960_);
lean_dec(v_second_963_);
v_nanos_968_ = lean_int_add(v___x_967_, v_nano_964_);
lean_dec(v_nano_964_);
lean_dec(v___x_967_);
v___x_969_ = lean_int_add(v_nanos_966_, v_nanos_968_);
lean_dec(v_nanos_968_);
lean_dec(v_nanos_966_);
v___x_970_ = l_Std_Time_Duration_ofNanoseconds(v___x_969_);
lean_dec(v___x_969_);
v___x_971_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_972_, lean_object* v_seconds_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_972_, v_seconds_973_);
lean_dec(v_seconds_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_975_, lean_object* v_milliseconds_976_){
_start:
{
lean_object* v___x_977_; lean_object* v_second_978_; lean_object* v_nano_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_second_983_; lean_object* v_nano_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_nanos_987_; lean_object* v___x_988_; lean_object* v_nanos_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_977_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_975_);
v_second_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_second_978_);
v_nano_979_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_nano_979_);
lean_dec_ref(v___x_977_);
v___x_980_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_981_ = lean_int_mul(v_milliseconds_976_, v___x_980_);
v___x_982_ = l_Std_Time_Duration_ofNanoseconds(v___x_981_);
lean_dec(v___x_981_);
v_second_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_second_983_);
v_nano_984_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_nano_984_);
lean_dec_ref(v___x_982_);
v___x_985_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_986_ = lean_int_mul(v_second_978_, v___x_985_);
lean_dec(v_second_978_);
v_nanos_987_ = lean_int_add(v___x_986_, v_nano_979_);
lean_dec(v_nano_979_);
lean_dec(v___x_986_);
v___x_988_ = lean_int_mul(v_second_983_, v___x_985_);
lean_dec(v_second_983_);
v_nanos_989_ = lean_int_add(v___x_988_, v_nano_984_);
lean_dec(v_nano_984_);
lean_dec(v___x_988_);
v___x_990_ = lean_int_add(v_nanos_987_, v_nanos_989_);
lean_dec(v_nanos_989_);
lean_dec(v_nanos_987_);
v___x_991_ = l_Std_Time_Duration_ofNanoseconds(v___x_990_);
lean_dec(v___x_990_);
v___x_992_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_993_, lean_object* v_milliseconds_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_993_, v_milliseconds_994_);
lean_dec(v_milliseconds_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_996_, lean_object* v_milliseconds_997_){
_start:
{
lean_object* v___x_998_; lean_object* v_second_999_; lean_object* v_nano_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_second_1005_; lean_object* v_nano_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_nanos_1009_; lean_object* v___x_1010_; lean_object* v_nanos_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_998_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_996_);
v_second_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_second_999_);
v_nano_1000_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_nano_1000_);
lean_dec_ref(v___x_998_);
v___x_1001_ = lean_int_neg(v_milliseconds_997_);
v___x_1002_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1003_ = lean_int_mul(v___x_1001_, v___x_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = l_Std_Time_Duration_ofNanoseconds(v___x_1003_);
lean_dec(v___x_1003_);
v_second_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_second_1005_);
v_nano_1006_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_nano_1006_);
lean_dec_ref(v___x_1004_);
v___x_1007_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1008_ = lean_int_mul(v_second_999_, v___x_1007_);
lean_dec(v_second_999_);
v_nanos_1009_ = lean_int_add(v___x_1008_, v_nano_1000_);
lean_dec(v_nano_1000_);
lean_dec(v___x_1008_);
v___x_1010_ = lean_int_mul(v_second_1005_, v___x_1007_);
lean_dec(v_second_1005_);
v_nanos_1011_ = lean_int_add(v___x_1010_, v_nano_1006_);
lean_dec(v_nano_1006_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_int_add(v_nanos_1009_, v_nanos_1011_);
lean_dec(v_nanos_1011_);
lean_dec(v_nanos_1009_);
v___x_1013_ = l_Std_Time_Duration_ofNanoseconds(v___x_1012_);
lean_dec(v___x_1012_);
v___x_1014_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1015_, lean_object* v_milliseconds_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1015_, v_milliseconds_1016_);
lean_dec(v_milliseconds_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1018_){
_start:
{
lean_object* v_date_1019_; lean_object* v_year_1020_; 
v_date_1019_ = lean_ctor_get(v_dt_1018_, 0);
v_year_1020_ = lean_ctor_get(v_date_1019_, 0);
lean_inc(v_year_1020_);
return v_year_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_Time_PlainDateTime_year(v_dt_1021_);
lean_dec_ref(v_dt_1021_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1023_){
_start:
{
lean_object* v_date_1024_; lean_object* v_month_1025_; 
v_date_1024_ = lean_ctor_get(v_dt_1023_, 0);
v_month_1025_ = lean_ctor_get(v_date_1024_, 1);
lean_inc(v_month_1025_);
return v_month_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_Time_PlainDateTime_month(v_dt_1026_);
lean_dec_ref(v_dt_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1028_){
_start:
{
lean_object* v_date_1029_; lean_object* v_day_1030_; 
v_date_1029_ = lean_ctor_get(v_dt_1028_, 0);
v_day_1030_ = lean_ctor_get(v_date_1029_, 2);
lean_inc(v_day_1030_);
return v_day_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_Time_PlainDateTime_day(v_dt_1031_);
lean_dec_ref(v_dt_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1033_){
_start:
{
lean_object* v_date_1034_; uint8_t v___x_1035_; 
v_date_1034_ = lean_ctor_get(v_dt_1033_, 0);
lean_inc_ref(v_date_1034_);
lean_dec_ref(v_dt_1033_);
v___x_1035_ = l_Std_Time_PlainDate_weekday(v_date_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Std_Time_PlainDateTime_weekday(v_dt_1036_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1039_){
_start:
{
lean_object* v_time_1040_; lean_object* v_hour_1041_; 
v_time_1040_ = lean_ctor_get(v_dt_1039_, 1);
v_hour_1041_ = lean_ctor_get(v_time_1040_, 0);
lean_inc(v_hour_1041_);
return v_hour_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_Time_PlainDateTime_hour(v_dt_1042_);
lean_dec_ref(v_dt_1042_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1044_){
_start:
{
lean_object* v_time_1045_; lean_object* v_minute_1046_; 
v_time_1045_ = lean_ctor_get(v_dt_1044_, 1);
v_minute_1046_ = lean_ctor_get(v_time_1045_, 1);
lean_inc(v_minute_1046_);
return v_minute_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_Time_PlainDateTime_minute(v_dt_1047_);
lean_dec_ref(v_dt_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1049_){
_start:
{
lean_object* v_time_1050_; lean_object* v_nanosecond_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_time_1050_ = lean_ctor_get(v_dt_1049_, 1);
v_nanosecond_1051_ = lean_ctor_get(v_time_1050_, 3);
v___x_1052_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1053_ = lean_int_ediv(v_nanosecond_1051_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1054_);
lean_dec_ref(v_dt_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1056_){
_start:
{
lean_object* v_time_1057_; lean_object* v_second_1058_; 
v_time_1057_ = lean_ctor_get(v_dt_1056_, 1);
v_second_1058_ = lean_ctor_get(v_time_1057_, 2);
lean_inc(v_second_1058_);
return v_second_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_Time_PlainDateTime_second(v_dt_1059_);
lean_dec_ref(v_dt_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1061_){
_start:
{
lean_object* v_time_1062_; lean_object* v_nanosecond_1063_; 
v_time_1062_ = lean_ctor_get(v_dt_1061_, 1);
v_nanosecond_1063_ = lean_ctor_get(v_time_1062_, 3);
lean_inc(v_nanosecond_1063_);
return v_nanosecond_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1064_);
lean_dec_ref(v_dt_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1066_){
_start:
{
lean_object* v_date_1067_; lean_object* v_year_1068_; uint8_t v___x_1069_; 
v_date_1067_ = lean_ctor_get(v_date_1066_, 0);
v_year_1068_ = lean_ctor_get(v_date_1067_, 0);
v___x_1069_ = l_Std_Time_Year_Offset_era(v_year_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Std_Time_PlainDateTime_era(v_date_1070_);
lean_dec_ref(v_date_1070_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1073_){
_start:
{
lean_object* v_date_1074_; lean_object* v_year_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_date_1074_ = lean_ctor_get(v_date_1073_, 0);
v_year_1075_ = lean_ctor_get(v_date_1074_, 0);
v___x_1076_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__0, &l_Std_Time_PlainDateTime_withDaysClip___closed__0_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__0);
v___x_1077_ = lean_int_mod(v_year_1075_, v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1079_ = lean_int_dec_eq(v___x_1077_, v___x_1078_);
lean_dec(v___x_1077_);
if (v___x_1079_ == 0)
{
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__1, &l_Std_Time_PlainDateTime_withDaysClip___closed__1_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__1);
v___x_1081_ = lean_int_mod(v_year_1075_, v___x_1080_);
v___x_1082_ = lean_int_dec_eq(v___x_1081_, v___x_1078_);
lean_dec(v___x_1081_);
if (v___x_1082_ == 0)
{
return v___x_1079_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__2, &l_Std_Time_PlainDateTime_withDaysClip___closed__2_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__2);
v___x_1084_ = lean_int_mod(v_year_1075_, v___x_1083_);
v___x_1085_ = lean_int_dec_eq(v___x_1084_, v___x_1078_);
lean_dec(v___x_1084_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object* v_date_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1086_);
lean_dec_ref(v_date_1086_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1089_, uint8_t v_firstDay_1090_, lean_object* v_minDays_1091_){
_start:
{
lean_object* v_date_1092_; lean_object* v___x_1093_; 
v_date_1092_ = lean_ctor_get(v_date_1089_, 0);
lean_inc_ref(v_date_1092_);
lean_dec_ref(v_date_1089_);
v___x_1093_ = l_Std_Time_PlainDate_weekOfYear(v_date_1092_, v_firstDay_1090_, v_minDays_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear___boxed(lean_object* v_date_1094_, lean_object* v_firstDay_1095_, lean_object* v_minDays_1096_){
_start:
{
uint8_t v_firstDay_boxed_1097_; lean_object* v_res_1098_; 
v_firstDay_boxed_1097_ = lean_unbox(v_firstDay_1095_);
v_res_1098_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_1094_, v_firstDay_boxed_1097_, v_minDays_1096_);
lean_dec(v_minDays_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object* v_date_1099_, uint8_t v_firstDay_1100_, lean_object* v_minDays_1101_){
_start:
{
lean_object* v_date_1102_; lean_object* v___x_1103_; 
v_date_1102_ = lean_ctor_get(v_date_1099_, 0);
lean_inc_ref(v_date_1102_);
lean_dec_ref(v_date_1099_);
v___x_1103_ = l_Std_Time_PlainDate_weekYear(v_date_1102_, v_firstDay_1100_, v_minDays_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object* v_date_1104_, lean_object* v_firstDay_1105_, lean_object* v_minDays_1106_){
_start:
{
uint8_t v_firstDay_boxed_1107_; lean_object* v_res_1108_; 
v_firstDay_boxed_1107_ = lean_unbox(v_firstDay_1105_);
v_res_1108_ = l_Std_Time_PlainDateTime_weekYear(v_date_1104_, v_firstDay_boxed_1107_, v_minDays_1106_);
lean_dec(v_minDays_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1109_){
_start:
{
lean_object* v_date_1110_; lean_object* v___x_1111_; 
v_date_1110_ = lean_ctor_get(v_date_1109_, 0);
v___x_1111_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1112_);
lean_dec_ref(v_date_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1114_, uint8_t v_firstDay_1115_){
_start:
{
lean_object* v_date_1116_; lean_object* v___x_1117_; 
v_date_1116_ = lean_ctor_get(v_date_1114_, 0);
lean_inc_ref(v_date_1116_);
lean_dec_ref(v_date_1114_);
v___x_1117_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1116_, v_firstDay_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1118_, lean_object* v_firstDay_1119_){
_start:
{
uint8_t v_firstDay_boxed_1120_; lean_object* v_res_1121_; 
v_firstDay_boxed_1120_ = lean_unbox(v_firstDay_1119_);
v_res_1121_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1118_, v_firstDay_boxed_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1122_){
_start:
{
lean_object* v_date_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1146_; 
v_date_1123_ = lean_ctor_get(v_date_1122_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_date_1122_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_date_1122_, 1);
lean_dec(v_unused_1147_);
v___x_1125_ = v_date_1122_;
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_date_1123_);
lean_dec(v_date_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_year_1127_; lean_object* v_month_1128_; lean_object* v_day_1129_; uint8_t v___y_1131_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_year_1127_ = lean_ctor_get(v_date_1123_, 0);
lean_inc(v_year_1127_);
v_month_1128_ = lean_ctor_get(v_date_1123_, 1);
lean_inc(v_month_1128_);
v_day_1129_ = lean_ctor_get(v_date_1123_, 2);
lean_inc(v_day_1129_);
lean_dec_ref(v_date_1123_);
v___x_1136_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__0, &l_Std_Time_PlainDateTime_withDaysClip___closed__0_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__0);
v___x_1137_ = lean_int_mod(v_year_1127_, v___x_1136_);
v___x_1138_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1139_ = lean_int_dec_eq(v___x_1137_, v___x_1138_);
lean_dec(v___x_1137_);
if (v___x_1139_ == 0)
{
lean_dec(v_year_1127_);
v___y_1131_ = v___x_1139_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__1, &l_Std_Time_PlainDateTime_withDaysClip___closed__1_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__1);
v___x_1141_ = lean_int_mod(v_year_1127_, v___x_1140_);
v___x_1142_ = lean_int_dec_eq(v___x_1141_, v___x_1138_);
lean_dec(v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec(v_year_1127_);
v___y_1131_ = v___x_1139_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_obj_once(&l_Std_Time_PlainDateTime_withDaysClip___closed__2, &l_Std_Time_PlainDateTime_withDaysClip___closed__2_once, _init_l_Std_Time_PlainDateTime_withDaysClip___closed__2);
v___x_1144_ = lean_int_mod(v_year_1127_, v___x_1143_);
lean_dec(v_year_1127_);
v___x_1145_ = lean_int_dec_eq(v___x_1144_, v___x_1138_);
lean_dec(v___x_1144_);
v___y_1131_ = v___x_1145_;
goto v___jp_1130_;
}
}
v___jp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_day_1129_);
lean_ctor_set(v___x_1125_, 0, v_month_1128_);
v___x_1133_ = v___x_1125_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_month_1128_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_day_1129_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_Time_ValidDate_dayOfYear(v___y_1131_, v___x_1133_);
lean_dec_ref(v___x_1133_);
return v___x_1134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object* v_date_1148_){
_start:
{
lean_object* v_date_1149_; lean_object* v___x_1150_; 
v_date_1149_ = lean_ctor_get(v_date_1148_, 0);
v___x_1150_ = l_Std_Time_PlainDate_quarter(v_date_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object* v_date_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_Time_PlainDateTime_quarter(v_date_1151_);
lean_dec_ref(v_date_1151_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object* v_date_1153_, lean_object* v_time_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_date_1153_);
lean_ctor_set(v___x_1155_, 1, v_time_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object* v_time_1156_, lean_object* v_date_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_date_1157_);
lean_ctor_set(v___x_1158_, 1, v_time_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object* v_x_1187_, lean_object* v_y_1188_){
_start:
{
lean_object* v_second_1189_; lean_object* v_nano_1190_; lean_object* v___x_1191_; lean_object* v_second_1192_; lean_object* v_nano_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_nanos_1196_; lean_object* v___x_1197_; lean_object* v_second_1198_; lean_object* v_nano_1199_; lean_object* v___x_1200_; lean_object* v_nanos_1201_; lean_object* v___x_1202_; lean_object* v_nanos_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_second_1189_ = lean_ctor_get(v_y_1188_, 0);
v_nano_1190_ = lean_ctor_get(v_y_1188_, 1);
v___x_1191_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1187_);
v_second_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_second_1192_);
v_nano_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_nano_1193_);
lean_dec_ref(v___x_1191_);
v___x_1194_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1195_ = lean_int_mul(v_second_1189_, v___x_1194_);
v_nanos_1196_ = lean_int_add(v___x_1195_, v_nano_1190_);
lean_dec(v___x_1195_);
v___x_1197_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1196_);
lean_dec(v_nanos_1196_);
v_second_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_second_1198_);
v_nano_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_nano_1199_);
lean_dec_ref(v___x_1197_);
v___x_1200_ = lean_int_mul(v_second_1192_, v___x_1194_);
lean_dec(v_second_1192_);
v_nanos_1201_ = lean_int_add(v___x_1200_, v_nano_1193_);
lean_dec(v_nano_1193_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_int_mul(v_second_1198_, v___x_1194_);
lean_dec(v_second_1198_);
v_nanos_1203_ = lean_int_add(v___x_1202_, v_nano_1199_);
lean_dec(v_nano_1199_);
lean_dec(v___x_1202_);
v___x_1204_ = lean_int_add(v_nanos_1201_, v_nanos_1203_);
lean_dec(v_nanos_1203_);
lean_dec(v_nanos_1201_);
v___x_1205_ = l_Std_Time_Duration_ofNanoseconds(v___x_1204_);
lean_dec(v___x_1204_);
v___x_1206_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1207_, lean_object* v_y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_1207_, v_y_1208_);
lean_dec_ref(v_y_1208_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = l_Std_Time_PlainTime_midnight;
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_date_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_1215_){
_start:
{
lean_object* v_date_1216_; 
v_date_1216_ = lean_ctor_get(v_pdt_1215_, 0);
lean_inc_ref(v_date_1216_);
return v_date_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_1217_);
lean_dec_ref(v_pdt_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_1219_){
_start:
{
lean_object* v_time_1220_; 
v_time_1220_ = lean_ctor_get(v_pdt_1219_, 1);
lean_inc_ref(v_time_1220_);
return v_time_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_1221_);
lean_dec_ref(v_pdt_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_1223_, lean_object* v_y_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v_second_1226_; lean_object* v_nano_1227_; lean_object* v___x_1228_; lean_object* v_second_1229_; lean_object* v_nano_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_nanos_1235_; lean_object* v___x_1236_; lean_object* v_nanos_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1225_ = l_Std_Time_PlainDateTime_toWallTime(v_y_1224_);
v_second_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_second_1226_);
v_nano_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_nano_1227_);
lean_dec_ref(v___x_1225_);
v___x_1228_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1223_);
v_second_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_second_1229_);
v_nano_1230_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_nano_1230_);
lean_dec_ref(v___x_1228_);
v___x_1231_ = lean_int_neg(v_second_1226_);
lean_dec(v_second_1226_);
v___x_1232_ = lean_int_neg(v_nano_1227_);
lean_dec(v_nano_1227_);
v___x_1233_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1234_ = lean_int_mul(v_second_1229_, v___x_1233_);
lean_dec(v_second_1229_);
v_nanos_1235_ = lean_int_add(v___x_1234_, v_nano_1230_);
lean_dec(v_nano_1230_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_int_mul(v___x_1231_, v___x_1233_);
lean_dec(v___x_1231_);
v_nanos_1237_ = lean_int_add(v___x_1236_, v___x_1232_);
lean_dec(v___x_1232_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_int_add(v_nanos_1235_, v_nanos_1237_);
lean_dec(v_nanos_1237_);
lean_dec(v_nanos_1235_);
v___x_1239_ = l_Std_Time_Duration_ofNanoseconds(v___x_1238_);
lean_dec(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object* v_pd_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1243_ = l_Std_Time_PlainDate_toEpochDay(v_pd_1242_);
v___x_1244_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1245_ = lean_int_mul(v___x_1243_, v___x_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object* v_wt_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v_date_1250_; 
v___x_1249_ = l_Std_Time_PlainDateTime_ofWallTime(v_wt_1248_);
v_date_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc_ref(v_date_1250_);
lean_dec_ref(v___x_1249_);
return v_date_1250_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1252_ = lean_int_neg(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_1253_, lean_object* v_y_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_nanos_1265_; lean_object* v___x_1266_; lean_object* v_nanos_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1255_ = l_Std_Time_PlainDate_toEpochDay(v_x_1253_);
v___x_1256_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1257_ = lean_int_mul(v___x_1255_, v___x_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1259_ = l_Std_Time_PlainDate_toEpochDay(v_y_1254_);
v___x_1260_ = lean_int_mul(v___x_1259_, v___x_1256_);
lean_dec(v___x_1259_);
v___x_1261_ = lean_int_neg(v___x_1260_);
lean_dec(v___x_1260_);
v___x_1262_ = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
v___x_1263_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1264_ = lean_int_mul(v___x_1257_, v___x_1263_);
lean_dec(v___x_1257_);
v_nanos_1265_ = lean_int_add(v___x_1264_, v___x_1258_);
lean_dec(v___x_1264_);
v___x_1266_ = lean_int_mul(v___x_1261_, v___x_1263_);
lean_dec(v___x_1261_);
v_nanos_1267_ = lean_int_add(v___x_1266_, v___x_1262_);
lean_dec(v___x_1266_);
v___x_1268_ = lean_int_add(v_nanos_1265_, v_nanos_1267_);
lean_dec(v_nanos_1267_);
lean_dec(v_nanos_1265_);
v___x_1269_ = l_Std_Time_Duration_ofNanoseconds(v___x_1268_);
lean_dec(v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object* v_date_1272_, lean_object* v_time_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_date_1272_);
lean_ctor_set(v___x_1274_, 1, v_time_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object* v_pt_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1275_);
v___x_1277_ = l_Std_Time_Duration_ofNanoseconds(v___x_1276_);
lean_dec(v___x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object* v_pt_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_Time_PlainTime_toWallTime(v_pt_1278_);
lean_dec_ref(v_pt_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object* v_wt_1280_){
_start:
{
lean_object* v_second_1281_; lean_object* v_nano_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_nanos_1285_; lean_object* v___x_1286_; 
v_second_1281_ = lean_ctor_get(v_wt_1280_, 0);
v_nano_1282_ = lean_ctor_get(v_wt_1280_, 1);
v___x_1283_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1284_ = lean_int_mul(v_second_1281_, v___x_1283_);
v_nanos_1285_ = lean_int_add(v___x_1284_, v_nano_1282_);
lean_dec(v___x_1284_);
v___x_1286_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1285_);
lean_dec(v_nanos_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object* v_wt_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_Time_PlainTime_ofWallTime(v_wt_1287_);
lean_dec_ref(v_wt_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object* v_time_1289_, lean_object* v_date_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_date_1290_);
lean_ctor_set(v___x_1291_, 1, v_time_1289_);
return v___x_1291_;
}
}
lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedPlainDateTime_default = _init_l_Std_Time_instInhabitedPlainDateTime_default();
lean_mark_persistent(l_Std_Time_instInhabitedPlainDateTime_default);
l_Std_Time_instInhabitedPlainDateTime = _init_l_Std_Time_instInhabitedPlainDateTime();
lean_mark_persistent(l_Std_Time_instInhabitedPlainDateTime);
l_Std_Time_instOrdPlainDateTime = _init_l_Std_Time_instOrdPlainDateTime();
lean_mark_persistent(l_Std_Time_instOrdPlainDateTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_DateTime_PlainDateTime(builtin);
}
#ifdef __cplusplus
}
#endif
