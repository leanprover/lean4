// Lean compiler output
// Module: Std.Time.DateTime.PlainDateTime
// Imports: public import Std.Time.DateTime.Timestamp
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainTime_toSeconds(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Fin_succ___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainDate_withWeekday(lean_object*, uint8_t);
lean_object* l_Std_Time_instReprPlainDate_repr___redArg(lean_object*);
lean_object* l_Std_Time_instReprPlainTime_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Std_Time_instDecidableEqPlainDate_decEq(lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqPlainTime_decEq(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
extern lean_object* l_Std_Time_instOrdPlainDate;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainDateTime_toTimestampAssumingUTC_spec__1(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainDateTime_toTimestampAssumingUTC_spec__0(lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__3;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__4;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__5;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__7;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__8;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__9;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__11;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__12;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__13;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__14;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__16;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__17;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__18;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__19;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__20;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__21;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__22;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__23;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__24;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__25;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__26;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__27;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__28;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__29;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__30;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__31;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__32;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofDaysSinceUNIXEpoch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainDateTime_toTimestampAssumingUTC_spec__1(lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Rat_ofInt(v_a_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(86400u);
v___x_235_ = lean_nat_to_int(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1000000000u);
v___x_237_ = lean_nat_to_int(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object* v_dt_238_){
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
v_days_242_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_240_);
v___x_243_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0);
v___x_244_ = lean_int_mul(v_days_242_, v___x_243_);
lean_dec(v_days_242_);
v___x_245_ = l_Std_Time_PlainTime_toSeconds(v_time_239_);
lean_dec_ref(v_time_239_);
v___x_246_ = lean_int_add(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainDateTime_toTimestampAssumingUTC_spec__0(lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_nat_to_int(v_a_251_);
v___x_253_ = l_Rat_ofInt(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(13u);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_mod(v___x_255_, v___x_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg(lean_object* v_as_x27_257_, lean_object* v_b_258_){
_start:
{
if (lean_obj_tag(v_as_x27_257_) == 0)
{
return v_b_258_;
}
else
{
lean_object* v_head_259_; lean_object* v_tail_260_; lean_object* v_fst_261_; lean_object* v_snd_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_278_; 
v_head_259_ = lean_ctor_get(v_as_x27_257_, 0);
v_tail_260_ = lean_ctor_get(v_as_x27_257_, 1);
v_fst_261_ = lean_ctor_get(v_b_258_, 0);
v_snd_262_ = lean_ctor_get(v_b_258_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_b_258_);
if (v_isSharedCheck_278_ == 0)
{
v___x_264_ = v_b_258_;
v_isShared_265_ = v_isSharedCheck_278_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snd_262_);
lean_inc(v_fst_261_);
lean_dec(v_b_258_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_278_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = lean_unsigned_to_nat(13u);
v___x_267_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___closed__0);
v___x_268_ = l_Fin_add(v___x_266_, v_snd_262_, v___x_267_);
lean_dec(v_snd_262_);
v___x_269_ = lean_int_dec_lt(v_fst_261_, v_head_259_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_int_sub(v_fst_261_, v_head_259_);
lean_dec(v_fst_261_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v___x_268_);
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_272_ = v___x_264_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_268_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_as_x27_257_ = v_tail_260_;
v_b_258_ = v___x_272_;
goto _start;
}
}
else
{
lean_object* v___x_276_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v___x_268_);
v___x_276_ = v___x_264_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_fst_261_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_268_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg___boxed(lean_object* v_as_x27_279_, lean_object* v_b_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg(v_as_x27_279_, v_b_280_);
lean_dec(v_as_x27_279_);
return v_res_281_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__0(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(11017u);
v___x_283_ = lean_nat_to_int(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(365u);
v___x_285_ = lean_nat_to_int(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(400u);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v___x_289_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1);
v___x_290_ = lean_int_mul(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__4(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(97u);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__5(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_daysPer400Y_295_; 
v___x_293_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__4, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__4_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__4);
v___x_294_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__3, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__3_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__3);
v_daysPer400Y_295_ = lean_int_add(v___x_294_, v___x_293_);
return v_daysPer400Y_295_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(100u);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__7(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v___x_299_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1);
v___x_300_ = lean_int_mul(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__8(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(24u);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__9(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_daysPer100Y_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__8, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__8_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__8);
v___x_304_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__7, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__7_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__7);
v_daysPer100Y_305_ = lean_int_add(v___x_304_, v___x_303_);
return v_daysPer100Y_305_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_to_int(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__11(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_309_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1);
v___x_310_ = lean_int_mul(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__12(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_daysPer4Y_313_; 
v___x_311_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_312_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__11, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__11_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__11);
v_daysPer4Y_313_ = lean_int_add(v___x_312_, v___x_311_);
return v_daysPer4Y_313_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__13(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(60u);
v___x_315_ = lean_nat_to_int(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__14(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(3600u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(31u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__16(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(29u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__17(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
v___x_323_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__16, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__16_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__16);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__18(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__17, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__17_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__17);
v___x_326_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__19(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__18, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__18_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__18);
v___x_329_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__20(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__19, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__19_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__19);
v___x_332_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__21(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__20, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__20_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__20);
v___x_335_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__22(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__21, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__21_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__21);
v___x_338_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__23(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__22, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__22_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__22);
v___x_341_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__24(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__23, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__23_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__23);
v___x_344_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__25(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__24, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__24_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__24);
v___x_347_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__26(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__25, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__25_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__25);
v___x_350_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__27(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__26, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__26_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__26);
v___x_353_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__28(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_months_357_; 
v___x_355_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__27, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__27_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__27);
v___x_356_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__15);
v_months_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_months_357_, 0, v___x_356_);
lean_ctor_set(v_months_357_, 1, v___x_355_);
return v_months_357_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__29(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_mon_360_; 
v___x_358_ = lean_unsigned_to_nat(13u);
v___x_359_ = lean_unsigned_to_nat(0u);
v_mon_360_ = lean_nat_mod(v___x_359_, v___x_358_);
return v_mon_360_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__30(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(2000u);
v___x_362_ = lean_nat_to_int(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__31(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(25u);
v___x_364_ = lean_nat_to_int(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__32(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_366_ = lean_int_neg(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object* v_stamp_367_){
_start:
{
lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v_second_389_; lean_object* v_nano_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_538_; 
v_second_389_ = lean_ctor_get(v_stamp_367_, 0);
v_nano_390_ = lean_ctor_get(v_stamp_367_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_stamp_367_);
if (v_isSharedCheck_538_ == 0)
{
v___x_392_ = v_stamp_367_;
v_isShared_393_ = v_isSharedCheck_538_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_nano_390_);
lean_inc(v_second_389_);
lean_dec(v_stamp_367_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_538_;
goto v_resetjp_391_;
}
v___jp_368_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_374_, 0, v___y_369_);
lean_ctor_set(v___x_374_, 1, v___y_372_);
lean_ctor_set(v___x_374_, 2, v___y_371_);
lean_ctor_set(v___x_374_, 3, v___y_370_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___y_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
v___jp_376_:
{
lean_object* v_max_385_; uint8_t v___x_386_; 
v_max_385_ = l_Std_Time_Month_Ordinal_days(v___y_384_, v___y_377_);
v___x_386_ = lean_int_dec_lt(v_max_385_, v___y_378_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_max_385_);
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v___y_382_);
lean_ctor_set(v___x_387_, 1, v___y_377_);
lean_ctor_set(v___x_387_, 2, v___y_378_);
v___y_369_ = v___y_379_;
v___y_370_ = v___y_380_;
v___y_371_ = v___y_381_;
v___y_372_ = v___y_383_;
v___y_373_ = v___x_387_;
goto v___jp_368_;
}
else
{
lean_object* v___x_388_; 
lean_dec(v___y_378_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___y_382_);
lean_ctor_set(v___x_388_, 1, v___y_377_);
lean_ctor_set(v___x_388_, 2, v_max_385_);
v___y_369_ = v___y_379_;
v___y_370_ = v___y_380_;
v___y_371_ = v___y_381_;
v___y_372_ = v___y_383_;
v___y_373_ = v___x_388_;
goto v___jp_368_;
}
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v_daysPer400Y_408_; lean_object* v___x_409_; lean_object* v_daysPer100Y_410_; lean_object* v___x_411_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_daysPer4Y_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v_hmon_436_; lean_object* v_year_437_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v_remYears_454_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v_quadrennialCycles_490_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_centenialCycles_500_; lean_object* v___y_508_; lean_object* v_quadracentennialCycles_509_; lean_object* v_remDays_510_; lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v_snd_524_; lean_object* v_secs_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_394_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__0, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__0_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__0);
v___x_395_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__1);
v___x_396_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v_daysPer400Y_408_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__5, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__5_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__5);
v___x_409_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v_daysPer100Y_410_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__9, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__9_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__9);
v___x_411_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v_daysPer4Y_428_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__12, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__12_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__12);
v___x_429_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_430_ = lean_int_mul(v_second_389_, v___x_429_);
lean_dec(v_second_389_);
v___x_431_ = lean_int_add(v___x_430_, v_nano_390_);
lean_dec(v_nano_390_);
lean_dec(v___x_430_);
v_secs_533_ = lean_int_div(v___x_431_, v___x_429_);
v___x_534_ = lean_int_mod(v___x_431_, v___x_429_);
v___x_535_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_536_ = lean_int_dec_lt(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
if (v___x_536_ == 0)
{
v_snd_524_ = v_secs_533_;
goto v___jp_523_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_int_sub(v_secs_533_, v___x_427_);
lean_dec(v_secs_533_);
v_snd_524_ = v___x_537_;
goto v___jp_523_;
}
v___jp_397_:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_int_mod(v___y_404_, v___x_396_);
v___x_407_ = lean_int_dec_eq(v___x_406_, v___y_402_);
lean_dec(v___y_402_);
lean_dec(v___x_406_);
v___y_377_ = v___y_398_;
v___y_378_ = v___y_399_;
v___y_379_ = v___y_400_;
v___y_380_ = v___y_401_;
v___y_381_ = v___y_403_;
v___y_382_ = v___y_404_;
v___y_383_ = v___y_405_;
v___y_384_ = v___x_407_;
goto v___jp_376_;
}
v___jp_412_:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_int_mod(v___y_417_, v___x_411_);
v___x_422_ = lean_nat_to_int(v___y_414_);
v___x_423_ = lean_int_dec_eq(v___x_421_, v___x_422_);
lean_dec(v___x_421_);
if (v___x_423_ == 0)
{
lean_dec(v___x_422_);
v___y_377_ = v___y_413_;
v___y_378_ = v___y_420_;
v___y_379_ = v___y_415_;
v___y_380_ = v___y_416_;
v___y_381_ = v___y_418_;
v___y_382_ = v___y_417_;
v___y_383_ = v___y_419_;
v___y_384_ = v___x_423_;
goto v___jp_376_;
}
else
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_int_mod(v___y_417_, v___x_409_);
v___x_425_ = lean_int_dec_eq(v___x_424_, v___x_422_);
lean_dec(v___x_424_);
if (v___x_425_ == 0)
{
if (v___x_423_ == 0)
{
v___y_398_ = v___y_413_;
v___y_399_ = v___y_420_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_416_;
v___y_402_ = v___x_422_;
v___y_403_ = v___y_418_;
v___y_404_ = v___y_417_;
v___y_405_ = v___y_419_;
goto v___jp_397_;
}
else
{
lean_dec(v___x_422_);
v___y_377_ = v___y_413_;
v___y_378_ = v___y_420_;
v___y_379_ = v___y_415_;
v___y_380_ = v___y_416_;
v___y_381_ = v___y_418_;
v___y_382_ = v___y_417_;
v___y_383_ = v___y_419_;
v___y_384_ = v___x_423_;
goto v___jp_376_;
}
}
else
{
v___y_398_ = v___y_413_;
v___y_399_ = v___y_420_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_416_;
v___y_402_ = v___x_422_;
v___y_403_ = v___y_418_;
v___y_404_ = v___y_417_;
v___y_405_ = v___y_419_;
goto v___jp_397_;
}
}
}
v___jp_432_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_438_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__13, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__13_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__13);
v___x_439_ = lean_int_emod(v___y_433_, v___x_438_);
v___x_440_ = lean_int_ediv(v___y_433_, v___x_438_);
v___x_441_ = lean_int_emod(v___x_440_, v___x_438_);
lean_dec(v___x_440_);
v___x_442_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__14, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__14_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__14);
v___x_443_ = lean_int_ediv(v___y_433_, v___x_442_);
lean_dec(v___y_433_);
v___x_444_ = lean_int_emod(v___x_431_, v___x_429_);
lean_dec(v___x_431_);
v___x_445_ = l_Fin_succ___redArg(v___y_435_);
lean_dec(v___y_435_);
v___x_446_ = lean_nat_dec_le(v___x_426_, v___x_445_);
if (v___x_446_ == 0)
{
lean_dec(v___x_445_);
v___y_413_ = v_hmon_436_;
v___y_414_ = v___y_434_;
v___y_415_ = v___x_443_;
v___y_416_ = v___x_444_;
v___y_417_ = v_year_437_;
v___y_418_ = v___x_439_;
v___y_419_ = v___x_441_;
v___y_420_ = v___x_427_;
goto v___jp_412_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_nat_to_int(v___x_445_);
v___y_413_ = v_hmon_436_;
v___y_414_ = v___y_434_;
v___y_415_ = v___x_443_;
v___y_416_ = v___x_444_;
v___y_417_ = v_year_437_;
v___y_418_ = v___x_439_;
v___y_419_ = v___x_441_;
v___y_420_ = v___x_447_;
goto v___jp_412_;
}
}
v___jp_448_:
{
lean_object* v___x_455_; lean_object* v_remDays_456_; lean_object* v___x_457_; lean_object* v_months_458_; lean_object* v___x_459_; lean_object* v_mon_460_; lean_object* v___x_462_; 
v___x_455_ = lean_int_mul(v_remYears_454_, v___x_395_);
v_remDays_456_ = lean_int_sub(v___y_451_, v___x_455_);
lean_dec(v___x_455_);
lean_dec(v___y_451_);
v___x_457_ = lean_unsigned_to_nat(31u);
v_months_458_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__28, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__28_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__28);
v___x_459_ = lean_unsigned_to_nat(0u);
v_mon_460_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__29, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__29_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__29);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_mon_460_);
lean_ctor_set(v___x_392_, 0, v_remDays_456_);
v___x_462_ = v___x_392_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_remDays_456_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_mon_460_);
v___x_462_ = v_reuseFailAlloc_484_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_year_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_463_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg(v_months_458_, v___x_462_);
v_fst_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_fst_464_);
v_snd_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___x_463_);
v___x_466_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__30, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__30_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__30);
v___x_467_ = lean_int_add(v___x_466_, v_remYears_454_);
lean_dec(v_remYears_454_);
v___x_468_ = lean_int_mul(v___x_411_, v___y_453_);
lean_dec(v___y_453_);
v___x_469_ = lean_int_add(v___x_467_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_int_mul(v___x_409_, v___y_450_);
lean_dec(v___y_450_);
v___x_471_ = lean_int_add(v___x_469_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_int_mul(v___x_396_, v___y_452_);
lean_dec(v___y_452_);
v_year_473_ = lean_int_add(v___x_471_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_471_);
v___x_474_ = l_Int_toNat(v_fst_464_);
lean_dec(v_fst_464_);
v___x_475_ = lean_nat_mod(v___x_474_, v___x_457_);
lean_dec(v___x_474_);
v___x_476_ = lean_unsigned_to_nat(10u);
v___x_477_ = lean_nat_dec_lt(v___x_476_, v_snd_465_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(2u);
v___x_479_ = lean_nat_add(v_snd_465_, v___x_478_);
lean_dec(v_snd_465_);
v___x_480_ = lean_nat_to_int(v___x_479_);
v___y_433_ = v___y_449_;
v___y_434_ = v___x_459_;
v___y_435_ = v___x_475_;
v_hmon_436_ = v___x_480_;
v_year_437_ = v_year_473_;
goto v___jp_432_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_int_add(v_year_473_, v___x_427_);
lean_dec(v_year_473_);
v___x_482_ = lean_nat_sub(v_snd_465_, v___x_476_);
lean_dec(v_snd_465_);
v___x_483_ = lean_nat_to_int(v___x_482_);
v___y_433_ = v___y_449_;
v___y_434_ = v___x_459_;
v___y_435_ = v___x_475_;
v_hmon_436_ = v___x_483_;
v_year_437_ = v___x_481_;
goto v___jp_432_;
}
}
}
v___jp_485_:
{
lean_object* v___x_491_; lean_object* v_remDays_492_; lean_object* v_remYears_493_; uint8_t v___x_494_; 
v___x_491_ = lean_int_mul(v_quadrennialCycles_490_, v_daysPer4Y_428_);
v_remDays_492_ = lean_int_sub(v___y_488_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v___y_488_);
v_remYears_493_ = lean_int_ediv(v_remDays_492_, v___x_395_);
v___x_494_ = lean_int_dec_eq(v_remYears_493_, v___x_411_);
if (v___x_494_ == 0)
{
v___y_449_ = v___y_487_;
v___y_450_ = v___y_486_;
v___y_451_ = v_remDays_492_;
v___y_452_ = v___y_489_;
v___y_453_ = v_quadrennialCycles_490_;
v_remYears_454_ = v_remYears_493_;
goto v___jp_448_;
}
else
{
lean_object* v_remYears_495_; 
v_remYears_495_ = lean_int_sub(v_remYears_493_, v___x_427_);
lean_dec(v_remYears_493_);
v___y_449_ = v___y_487_;
v___y_450_ = v___y_486_;
v___y_451_ = v_remDays_492_;
v___y_452_ = v___y_489_;
v___y_453_ = v_quadrennialCycles_490_;
v_remYears_454_ = v_remYears_495_;
goto v___jp_448_;
}
}
v___jp_496_:
{
lean_object* v___x_501_; lean_object* v_remDays_502_; lean_object* v_quadrennialCycles_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_501_ = lean_int_mul(v_centenialCycles_500_, v_daysPer100Y_410_);
v_remDays_502_ = lean_int_sub(v___y_499_, v___x_501_);
lean_dec(v___x_501_);
lean_dec(v___y_499_);
v_quadrennialCycles_503_ = lean_int_ediv(v_remDays_502_, v_daysPer4Y_428_);
v___x_504_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__31, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__31_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__31);
v___x_505_ = lean_int_dec_eq(v_quadrennialCycles_503_, v___x_504_);
if (v___x_505_ == 0)
{
v___y_486_ = v_centenialCycles_500_;
v___y_487_ = v___y_497_;
v___y_488_ = v_remDays_502_;
v___y_489_ = v___y_498_;
v_quadrennialCycles_490_ = v_quadrennialCycles_503_;
goto v___jp_485_;
}
else
{
lean_object* v_quadrennialCycles_506_; 
v_quadrennialCycles_506_ = lean_int_sub(v_quadrennialCycles_503_, v___x_427_);
lean_dec(v_quadrennialCycles_503_);
v___y_486_ = v_centenialCycles_500_;
v___y_487_ = v___y_497_;
v___y_488_ = v_remDays_502_;
v___y_489_ = v___y_498_;
v_quadrennialCycles_490_ = v_quadrennialCycles_506_;
goto v___jp_485_;
}
}
v___jp_507_:
{
lean_object* v_centenialCycles_511_; uint8_t v___x_512_; 
v_centenialCycles_511_ = lean_int_ediv(v_remDays_510_, v_daysPer100Y_410_);
v___x_512_ = lean_int_dec_eq(v_centenialCycles_511_, v___x_411_);
if (v___x_512_ == 0)
{
v___y_497_ = v___y_508_;
v___y_498_ = v_quadracentennialCycles_509_;
v___y_499_ = v_remDays_510_;
v_centenialCycles_500_ = v_centenialCycles_511_;
goto v___jp_496_;
}
else
{
lean_object* v_centenialCycles_513_; 
v_centenialCycles_513_ = lean_int_sub(v_centenialCycles_511_, v___x_427_);
lean_dec(v_centenialCycles_511_);
v___y_497_ = v___y_508_;
v___y_498_ = v_quadracentennialCycles_509_;
v___y_499_ = v_remDays_510_;
v_centenialCycles_500_ = v_centenialCycles_513_;
goto v___jp_496_;
}
}
v___jp_514_:
{
lean_object* v_quadracentennialCycles_517_; lean_object* v_remDays_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_quadracentennialCycles_517_ = lean_int_ediv(v_snd_516_, v_daysPer400Y_408_);
v_remDays_518_ = lean_int_emod(v_snd_516_, v_daysPer400Y_408_);
lean_dec(v_snd_516_);
v___x_519_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_520_ = lean_int_dec_lt(v_remDays_518_, v___x_519_);
if (v___x_520_ == 0)
{
v___y_508_ = v_fst_515_;
v_quadracentennialCycles_509_ = v_quadracentennialCycles_517_;
v_remDays_510_ = v_remDays_518_;
goto v___jp_507_;
}
else
{
lean_object* v_remDays_521_; lean_object* v_quadracentennialCycles_522_; 
v_remDays_521_ = lean_int_add(v_remDays_518_, v_daysPer400Y_408_);
lean_dec(v_remDays_518_);
v_quadracentennialCycles_522_ = lean_int_sub(v_quadracentennialCycles_517_, v___x_427_);
lean_dec(v_quadracentennialCycles_517_);
v___y_508_ = v_fst_515_;
v_quadracentennialCycles_509_ = v_quadracentennialCycles_522_;
v_remDays_510_ = v_remDays_521_;
goto v___jp_507_;
}
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v_boundedDaysSinceEpoch_526_; lean_object* v_rawDays_527_; lean_object* v_h_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_525_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__0);
v_boundedDaysSinceEpoch_526_ = lean_int_div(v_snd_524_, v___x_525_);
v_rawDays_527_ = lean_int_sub(v_boundedDaysSinceEpoch_526_, v___x_394_);
lean_dec(v_boundedDaysSinceEpoch_526_);
v_h_528_ = lean_int_mod(v_snd_524_, v___x_525_);
lean_dec(v_snd_524_);
v___x_529_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__32, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__32_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__32);
v___x_530_ = lean_int_dec_le(v_h_528_, v___x_529_);
if (v___x_530_ == 0)
{
v_fst_515_ = v_h_528_;
v_snd_516_ = v_rawDays_527_;
goto v___jp_514_;
}
else
{
lean_object* v___x_531_; lean_object* v_rawDays_532_; 
v___x_531_ = lean_int_add(v_h_528_, v___x_525_);
lean_dec(v_h_528_);
v_rawDays_532_ = lean_int_sub(v_rawDays_527_, v___x_427_);
lean_dec(v_rawDays_527_);
v_fst_515_ = v___x_531_;
v_snd_516_ = v_rawDays_532_;
goto v___jp_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0(lean_object* v_as_539_, lean_object* v_as_x27_540_, lean_object* v_b_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___redArg(v_as_x27_540_, v_b_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0___boxed(lean_object* v_as_544_, lean_object* v_as_x27_545_, lean_object* v_b_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofTimestampAssumingUTC_spec__0(v_as_544_, v_as_x27_545_, v_b_546_, v_a_547_);
lean_dec(v_as_x27_545_);
lean_dec(v_as_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDaysSinceUNIXEpoch(lean_object* v_pdt_549_){
_start:
{
lean_object* v_date_550_; lean_object* v___x_551_; 
v_date_550_ = lean_ctor_get(v_pdt_549_, 0);
lean_inc_ref(v_date_550_);
lean_dec_ref(v_pdt_549_);
v___x_551_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofDaysSinceUNIXEpoch(lean_object* v_days_552_, lean_object* v_time_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_days_552_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_time_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofDaysSinceUNIXEpoch___boxed(lean_object* v_days_556_, lean_object* v_time_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Time_PlainDateTime_ofDaysSinceUNIXEpoch(v_days_556_, v_time_557_);
lean_dec(v_days_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_559_, uint8_t v_desiredWeekday_560_){
_start:
{
lean_object* v_date_561_; lean_object* v_time_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
v_date_561_ = lean_ctor_get(v_dt_559_, 0);
v_time_562_ = lean_ctor_get(v_dt_559_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_dt_559_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_dt_559_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_time_562_);
lean_inc(v_date_561_);
lean_dec(v_dt_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l_Std_Time_PlainDate_withWeekday(v_date_561_, v_desiredWeekday_560_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_time_562_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_571_, lean_object* v_desiredWeekday_572_){
_start:
{
uint8_t v_desiredWeekday_boxed_573_; lean_object* v_res_574_; 
v_desiredWeekday_boxed_573_ = lean_unbox(v_desiredWeekday_572_);
v_res_574_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_571_, v_desiredWeekday_boxed_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_575_, lean_object* v_days_576_){
_start:
{
lean_object* v_date_577_; lean_object* v_time_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_616_; 
v_date_577_ = lean_ctor_get(v_dt_575_, 0);
v_time_578_ = lean_ctor_get(v_dt_575_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_dt_575_);
if (v_isSharedCheck_616_ == 0)
{
v___x_580_ = v_dt_575_;
v_isShared_581_ = v_isSharedCheck_616_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_time_578_);
lean_inc(v_date_577_);
lean_dec(v_dt_575_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_616_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_year_582_; lean_object* v_month_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_614_; 
v_year_582_ = lean_ctor_get(v_date_577_, 0);
v_month_583_ = lean_ctor_get(v_date_577_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_date_577_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_date_577_, 2);
lean_dec(v_unused_615_);
v___x_585_ = v_date_577_;
v_isShared_586_ = v_isSharedCheck_614_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_month_583_);
lean_inc(v_year_582_);
lean_dec(v_date_577_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_614_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
uint8_t v___y_588_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_610_; 
v___x_603_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_604_ = lean_int_mod(v_year_582_, v___x_603_);
v___x_605_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_610_ = lean_int_dec_eq(v___x_604_, v___x_605_);
lean_dec(v___x_604_);
if (v___x_610_ == 0)
{
v___y_588_ = v___x_610_;
goto v___jp_587_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v___x_612_ = lean_int_mod(v_year_582_, v___x_611_);
v___x_613_ = lean_int_dec_eq(v___x_612_, v___x_605_);
lean_dec(v___x_612_);
if (v___x_613_ == 0)
{
if (v___x_610_ == 0)
{
goto v___jp_606_;
}
else
{
v___y_588_ = v___x_610_;
goto v___jp_587_;
}
}
else
{
goto v___jp_606_;
}
}
v___jp_587_:
{
lean_object* v_max_589_; uint8_t v___x_590_; 
v_max_589_ = l_Std_Time_Month_Ordinal_days(v___y_588_, v_month_583_);
v___x_590_ = lean_int_dec_lt(v_max_589_, v_days_576_);
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v_max_589_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 2, v_days_576_);
v___x_592_ = v___x_585_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_year_582_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_month_583_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_days_576_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_592_);
v___x_594_ = v___x_580_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_time_578_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v_days_576_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 2, v_max_589_);
v___x_598_ = v___x_585_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_year_582_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_month_583_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_max_589_);
v___x_598_ = v_reuseFailAlloc_602_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_598_);
v___x_600_ = v___x_580_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_time_578_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
v___jp_606_:
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v___x_608_ = lean_int_mod(v_year_582_, v___x_607_);
v___x_609_ = lean_int_dec_eq(v___x_608_, v___x_605_);
lean_dec(v___x_608_);
v___y_588_ = v___x_609_;
goto v___jp_587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_617_, lean_object* v_days_618_){
_start:
{
lean_object* v_date_619_; lean_object* v_time_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_630_; 
v_date_619_ = lean_ctor_get(v_dt_617_, 0);
v_time_620_ = lean_ctor_get(v_dt_617_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_dt_617_);
if (v_isSharedCheck_630_ == 0)
{
v___x_622_ = v_dt_617_;
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_time_620_);
lean_inc(v_date_619_);
lean_dec(v_dt_617_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_year_624_; lean_object* v_month_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v_year_624_ = lean_ctor_get(v_date_619_, 0);
lean_inc(v_year_624_);
v_month_625_ = lean_ctor_get(v_date_619_, 1);
lean_inc(v_month_625_);
lean_dec_ref(v_date_619_);
v___x_626_ = l_Std_Time_PlainDate_rollOver(v_year_624_, v_month_625_, v_days_618_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_626_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_time_620_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_631_, lean_object* v_days_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_631_, v_days_632_);
lean_dec(v_days_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_634_, lean_object* v_month_635_){
_start:
{
lean_object* v_date_636_; lean_object* v_time_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_675_; 
v_date_636_ = lean_ctor_get(v_dt_634_, 0);
v_time_637_ = lean_ctor_get(v_dt_634_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_dt_634_);
if (v_isSharedCheck_675_ == 0)
{
v___x_639_ = v_dt_634_;
v_isShared_640_ = v_isSharedCheck_675_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_time_637_);
lean_inc(v_date_636_);
lean_dec(v_dt_634_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_675_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_year_641_; lean_object* v_day_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_673_; 
v_year_641_ = lean_ctor_get(v_date_636_, 0);
v_day_642_ = lean_ctor_get(v_date_636_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_date_636_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_date_636_, 1);
lean_dec(v_unused_674_);
v___x_644_ = v_date_636_;
v_isShared_645_ = v_isSharedCheck_673_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_day_642_);
lean_inc(v_year_641_);
lean_dec(v_date_636_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_673_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___y_647_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_669_; 
v___x_662_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_663_ = lean_int_mod(v_year_641_, v___x_662_);
v___x_664_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_669_ = lean_int_dec_eq(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
if (v___x_669_ == 0)
{
v___y_647_ = v___x_669_;
goto v___jp_646_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v___x_671_ = lean_int_mod(v_year_641_, v___x_670_);
v___x_672_ = lean_int_dec_eq(v___x_671_, v___x_664_);
lean_dec(v___x_671_);
if (v___x_672_ == 0)
{
if (v___x_669_ == 0)
{
goto v___jp_665_;
}
else
{
v___y_647_ = v___x_669_;
goto v___jp_646_;
}
}
else
{
goto v___jp_665_;
}
}
v___jp_646_:
{
lean_object* v_max_648_; uint8_t v___x_649_; 
v_max_648_ = l_Std_Time_Month_Ordinal_days(v___y_647_, v_month_635_);
v___x_649_ = lean_int_dec_lt(v_max_648_, v_day_642_);
if (v___x_649_ == 0)
{
lean_object* v___x_651_; 
lean_dec(v_max_648_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v_month_635_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_year_641_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_month_635_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_day_642_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_651_);
v___x_653_ = v___x_639_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_time_637_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
lean_object* v___x_657_; 
lean_dec(v_day_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 2, v_max_648_);
lean_ctor_set(v___x_644_, 1, v_month_635_);
v___x_657_ = v___x_644_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_year_641_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_month_635_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_max_648_);
v___x_657_ = v_reuseFailAlloc_661_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_659_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_657_);
v___x_659_ = v___x_639_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_time_637_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v___x_667_ = lean_int_mod(v_year_641_, v___x_666_);
v___x_668_ = lean_int_dec_eq(v___x_667_, v___x_664_);
lean_dec(v___x_667_);
v___y_647_ = v___x_668_;
goto v___jp_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_676_, lean_object* v_month_677_){
_start:
{
lean_object* v_date_678_; lean_object* v_time_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v_date_678_ = lean_ctor_get(v_dt_676_, 0);
v_time_679_ = lean_ctor_get(v_dt_676_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_dt_676_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v_dt_676_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_time_679_);
lean_inc(v_date_678_);
lean_dec(v_dt_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_year_683_; lean_object* v_day_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v_year_683_ = lean_ctor_get(v_date_678_, 0);
lean_inc(v_year_683_);
v_day_684_ = lean_ctor_get(v_date_678_, 2);
lean_inc(v_day_684_);
lean_dec_ref(v_date_678_);
v___x_685_ = l_Std_Time_PlainDate_rollOver(v_year_683_, v_month_677_, v_day_684_);
lean_dec(v_day_684_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_685_);
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_time_679_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_690_, lean_object* v_year_691_){
_start:
{
lean_object* v_date_692_; lean_object* v_time_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_731_; 
v_date_692_ = lean_ctor_get(v_dt_690_, 0);
v_time_693_ = lean_ctor_get(v_dt_690_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_dt_690_);
if (v_isSharedCheck_731_ == 0)
{
v___x_695_ = v_dt_690_;
v_isShared_696_ = v_isSharedCheck_731_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_time_693_);
lean_inc(v_date_692_);
lean_dec(v_dt_690_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_731_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_month_697_; lean_object* v_day_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_729_; 
v_month_697_ = lean_ctor_get(v_date_692_, 1);
v_day_698_ = lean_ctor_get(v_date_692_, 2);
v_isSharedCheck_729_ = !lean_is_exclusive(v_date_692_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_date_692_, 0);
lean_dec(v_unused_730_);
v___x_700_ = v_date_692_;
v_isShared_701_ = v_isSharedCheck_729_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_day_698_);
lean_inc(v_month_697_);
lean_dec(v_date_692_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_729_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___y_703_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_725_; 
v___x_718_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_719_ = lean_int_mod(v_year_691_, v___x_718_);
v___x_720_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_725_ = lean_int_dec_eq(v___x_719_, v___x_720_);
lean_dec(v___x_719_);
if (v___x_725_ == 0)
{
v___y_703_ = v___x_725_;
goto v___jp_702_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v___x_727_ = lean_int_mod(v_year_691_, v___x_726_);
v___x_728_ = lean_int_dec_eq(v___x_727_, v___x_720_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
if (v___x_725_ == 0)
{
goto v___jp_721_;
}
else
{
v___y_703_ = v___x_725_;
goto v___jp_702_;
}
}
else
{
goto v___jp_721_;
}
}
v___jp_702_:
{
lean_object* v_max_704_; uint8_t v___x_705_; 
v_max_704_ = l_Std_Time_Month_Ordinal_days(v___y_703_, v_month_697_);
v___x_705_ = lean_int_dec_lt(v_max_704_, v_day_698_);
if (v___x_705_ == 0)
{
lean_object* v___x_707_; 
lean_dec(v_max_704_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v_year_691_);
v___x_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_year_691_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_month_697_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_day_698_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_707_);
v___x_709_ = v___x_695_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_time_693_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v___x_713_; 
lean_dec(v_day_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 2, v_max_704_);
lean_ctor_set(v___x_700_, 0, v_year_691_);
v___x_713_ = v___x_700_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_year_691_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_month_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_max_704_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_713_);
v___x_715_ = v___x_695_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_time_693_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v___x_723_ = lean_int_mod(v_year_691_, v___x_722_);
v___x_724_ = lean_int_dec_eq(v___x_723_, v___x_720_);
lean_dec(v___x_723_);
v___y_703_ = v___x_724_;
goto v___jp_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_732_, lean_object* v_year_733_){
_start:
{
lean_object* v_date_734_; lean_object* v_time_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_745_; 
v_date_734_ = lean_ctor_get(v_dt_732_, 0);
v_time_735_ = lean_ctor_get(v_dt_732_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_dt_732_);
if (v_isSharedCheck_745_ == 0)
{
v___x_737_ = v_dt_732_;
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_time_735_);
lean_inc(v_date_734_);
lean_dec(v_dt_732_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_month_739_; lean_object* v_day_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v_month_739_ = lean_ctor_get(v_date_734_, 1);
lean_inc(v_month_739_);
v_day_740_ = lean_ctor_get(v_date_734_, 2);
lean_inc(v_day_740_);
lean_dec_ref(v_date_734_);
v___x_741_ = l_Std_Time_PlainDate_rollOver(v_year_733_, v_month_739_, v_day_740_);
lean_dec(v_day_740_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_741_);
v___x_743_ = v___x_737_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_time_735_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_746_, lean_object* v_hour_747_){
_start:
{
lean_object* v_time_748_; lean_object* v_date_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_767_; 
v_time_748_ = lean_ctor_get(v_dt_746_, 1);
v_date_749_ = lean_ctor_get(v_dt_746_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_dt_746_);
if (v_isSharedCheck_767_ == 0)
{
v___x_751_ = v_dt_746_;
v_isShared_752_ = v_isSharedCheck_767_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_time_748_);
lean_inc(v_date_749_);
lean_dec(v_dt_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_767_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_minute_753_; lean_object* v_second_754_; lean_object* v_nanosecond_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_765_; 
v_minute_753_ = lean_ctor_get(v_time_748_, 1);
v_second_754_ = lean_ctor_get(v_time_748_, 2);
v_nanosecond_755_ = lean_ctor_get(v_time_748_, 3);
v_isSharedCheck_765_ = !lean_is_exclusive(v_time_748_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_time_748_, 0);
lean_dec(v_unused_766_);
v___x_757_ = v_time_748_;
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_nanosecond_755_);
lean_inc(v_second_754_);
lean_inc(v_minute_753_);
lean_dec(v_time_748_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_hour_747_);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_hour_747_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_minute_753_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_second_754_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_nanosecond_755_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_760_);
v___x_762_ = v___x_751_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_date_749_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_768_, lean_object* v_minute_769_){
_start:
{
lean_object* v_time_770_; lean_object* v_date_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_789_; 
v_time_770_ = lean_ctor_get(v_dt_768_, 1);
v_date_771_ = lean_ctor_get(v_dt_768_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_dt_768_);
if (v_isSharedCheck_789_ == 0)
{
v___x_773_ = v_dt_768_;
v_isShared_774_ = v_isSharedCheck_789_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_time_770_);
lean_inc(v_date_771_);
lean_dec(v_dt_768_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_789_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_hour_775_; lean_object* v_second_776_; lean_object* v_nanosecond_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_787_; 
v_hour_775_ = lean_ctor_get(v_time_770_, 0);
v_second_776_ = lean_ctor_get(v_time_770_, 2);
v_nanosecond_777_ = lean_ctor_get(v_time_770_, 3);
v_isSharedCheck_787_ = !lean_is_exclusive(v_time_770_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_time_770_, 1);
lean_dec(v_unused_788_);
v___x_779_ = v_time_770_;
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_nanosecond_777_);
lean_inc(v_second_776_);
lean_inc(v_hour_775_);
lean_dec(v_time_770_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_minute_769_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_hour_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_minute_769_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_second_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_nanosecond_777_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_782_);
v___x_784_ = v___x_773_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_date_771_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_790_, lean_object* v_second_791_){
_start:
{
lean_object* v_time_792_; lean_object* v_date_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_811_; 
v_time_792_ = lean_ctor_get(v_dt_790_, 1);
v_date_793_ = lean_ctor_get(v_dt_790_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_dt_790_);
if (v_isSharedCheck_811_ == 0)
{
v___x_795_ = v_dt_790_;
v_isShared_796_ = v_isSharedCheck_811_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_time_792_);
lean_inc(v_date_793_);
lean_dec(v_dt_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_811_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_hour_797_; lean_object* v_minute_798_; lean_object* v_nanosecond_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_809_; 
v_hour_797_ = lean_ctor_get(v_time_792_, 0);
v_minute_798_ = lean_ctor_get(v_time_792_, 1);
v_nanosecond_799_ = lean_ctor_get(v_time_792_, 3);
v_isSharedCheck_809_ = !lean_is_exclusive(v_time_792_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_time_792_, 2);
lean_dec(v_unused_810_);
v___x_801_ = v_time_792_;
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_nanosecond_799_);
lean_inc(v_minute_798_);
lean_inc(v_hour_797_);
lean_dec(v_time_792_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_809_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 2, v_second_791_);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_hour_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_minute_798_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_second_791_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_nanosecond_799_);
v___x_804_ = v_reuseFailAlloc_808_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_804_);
v___x_806_ = v___x_795_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_date_793_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(1000u);
v___x_813_ = lean_nat_to_int(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(1000000u);
v___x_815_ = lean_nat_to_int(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_816_, lean_object* v_millis_817_){
_start:
{
lean_object* v_time_818_; lean_object* v_date_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_842_; 
v_time_818_ = lean_ctor_get(v_dt_816_, 1);
v_date_819_ = lean_ctor_get(v_dt_816_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_dt_816_);
if (v_isSharedCheck_842_ == 0)
{
v___x_821_ = v_dt_816_;
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_time_818_);
lean_inc(v_date_819_);
lean_dec(v_dt_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_hour_823_; lean_object* v_minute_824_; lean_object* v_second_825_; lean_object* v_nanosecond_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_841_; 
v_hour_823_ = lean_ctor_get(v_time_818_, 0);
v_minute_824_ = lean_ctor_get(v_time_818_, 1);
v_second_825_ = lean_ctor_get(v_time_818_, 2);
v_nanosecond_826_ = lean_ctor_get(v_time_818_, 3);
v_isSharedCheck_841_ = !lean_is_exclusive(v_time_818_);
if (v_isSharedCheck_841_ == 0)
{
v___x_828_ = v_time_818_;
v_isShared_829_ = v_isSharedCheck_841_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_nanosecond_826_);
lean_inc(v_second_825_);
lean_inc(v_minute_824_);
lean_inc(v_hour_823_);
lean_dec(v_time_818_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_841_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_830_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_831_ = lean_int_emod(v_nanosecond_826_, v___x_830_);
lean_dec(v_nanosecond_826_);
v___x_832_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_833_ = lean_int_mul(v_millis_817_, v___x_832_);
v___x_834_ = lean_int_add(v___x_833_, v___x_831_);
lean_dec(v___x_831_);
lean_dec(v___x_833_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 3, v___x_834_);
v___x_836_ = v___x_828_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_hour_823_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_minute_824_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_second_825_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v___x_834_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_836_);
v___x_838_ = v___x_821_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_date_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_843_, lean_object* v_millis_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_843_, v_millis_844_);
lean_dec(v_millis_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_846_, lean_object* v_nano_847_){
_start:
{
lean_object* v_time_848_; lean_object* v_date_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_867_; 
v_time_848_ = lean_ctor_get(v_dt_846_, 1);
v_date_849_ = lean_ctor_get(v_dt_846_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_dt_846_);
if (v_isSharedCheck_867_ == 0)
{
v___x_851_ = v_dt_846_;
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_time_848_);
lean_inc(v_date_849_);
lean_dec(v_dt_846_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_hour_853_; lean_object* v_minute_854_; lean_object* v_second_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_hour_853_ = lean_ctor_get(v_time_848_, 0);
v_minute_854_ = lean_ctor_get(v_time_848_, 1);
v_second_855_ = lean_ctor_get(v_time_848_, 2);
v_isSharedCheck_865_ = !lean_is_exclusive(v_time_848_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_time_848_, 3);
lean_dec(v_unused_866_);
v___x_857_ = v_time_848_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_second_855_);
lean_inc(v_minute_854_);
lean_inc(v_hour_853_);
lean_dec(v_time_848_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 3, v_nano_847_);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_hour_853_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_minute_854_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_second_855_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_nano_847_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_860_);
v___x_862_ = v___x_851_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_date_849_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_868_, lean_object* v_days_869_){
_start:
{
lean_object* v_date_870_; lean_object* v_time_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_881_; 
v_date_870_ = lean_ctor_get(v_dt_868_, 0);
v_time_871_ = lean_ctor_get(v_dt_868_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_dt_868_);
if (v_isSharedCheck_881_ == 0)
{
v___x_873_ = v_dt_868_;
v_isShared_874_ = v_isSharedCheck_881_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_time_871_);
lean_inc(v_date_870_);
lean_dec(v_dt_868_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_881_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_dateDays_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v_dateDays_875_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_870_);
v___x_876_ = lean_int_add(v_dateDays_875_, v_days_869_);
lean_dec(v_dateDays_875_);
v___x_877_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_876_);
lean_dec(v___x_876_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_time_871_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_882_, lean_object* v_days_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Time_PlainDateTime_addDays(v_dt_882_, v_days_883_);
lean_dec(v_days_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_885_, lean_object* v_days_886_){
_start:
{
lean_object* v_date_887_; lean_object* v_time_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_899_; 
v_date_887_ = lean_ctor_get(v_dt_885_, 0);
v_time_888_ = lean_ctor_get(v_dt_885_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_dt_885_);
if (v_isSharedCheck_899_ == 0)
{
v___x_890_ = v_dt_885_;
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_time_888_);
lean_inc(v_date_887_);
lean_dec(v_dt_885_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v_dateDays_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_892_ = lean_int_neg(v_days_886_);
v_dateDays_893_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_887_);
v___x_894_ = lean_int_add(v_dateDays_893_, v___x_892_);
lean_dec(v___x_892_);
lean_dec(v_dateDays_893_);
v___x_895_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_894_);
lean_dec(v___x_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_895_);
v___x_897_ = v___x_890_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_time_888_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_900_, lean_object* v_days_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Time_PlainDateTime_subDays(v_dt_900_, v_days_901_);
lean_dec(v_days_901_);
return v_res_902_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(7u);
v___x_904_ = lean_nat_to_int(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_905_, lean_object* v_weeks_906_){
_start:
{
lean_object* v_date_907_; lean_object* v_time_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_920_; 
v_date_907_ = lean_ctor_get(v_dt_905_, 0);
v_time_908_ = lean_ctor_get(v_dt_905_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_dt_905_);
if (v_isSharedCheck_920_ == 0)
{
v___x_910_ = v_dt_905_;
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_time_908_);
lean_inc(v_date_907_);
lean_dec(v_dt_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_dateDays_912_; lean_object* v___x_913_; lean_object* v_daysToAdd_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v_dateDays_912_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_907_);
v___x_913_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_914_ = lean_int_mul(v_weeks_906_, v___x_913_);
v___x_915_ = lean_int_add(v_dateDays_912_, v_daysToAdd_914_);
lean_dec(v_daysToAdd_914_);
lean_dec(v_dateDays_912_);
v___x_916_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_915_);
lean_dec(v___x_915_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_916_);
v___x_918_ = v___x_910_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_time_908_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_921_, lean_object* v_weeks_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_921_, v_weeks_922_);
lean_dec(v_weeks_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_924_, lean_object* v_weeks_925_){
_start:
{
lean_object* v_date_926_; lean_object* v_time_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_940_; 
v_date_926_ = lean_ctor_get(v_dt_924_, 0);
v_time_927_ = lean_ctor_get(v_dt_924_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_dt_924_);
if (v_isSharedCheck_940_ == 0)
{
v___x_929_ = v_dt_924_;
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_time_927_);
lean_inc(v_date_926_);
lean_dec(v_dt_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v_dateDays_932_; lean_object* v___x_933_; lean_object* v_daysToAdd_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_931_ = lean_int_neg(v_weeks_925_);
v_dateDays_932_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_926_);
v___x_933_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_934_ = lean_int_mul(v___x_931_, v___x_933_);
lean_dec(v___x_931_);
v___x_935_ = lean_int_add(v_dateDays_932_, v_daysToAdd_934_);
lean_dec(v_daysToAdd_934_);
lean_dec(v_dateDays_932_);
v___x_936_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_935_);
lean_dec(v___x_935_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_936_);
v___x_938_ = v___x_929_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_time_927_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_941_, lean_object* v_weeks_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_941_, v_weeks_942_);
lean_dec(v_weeks_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_944_, lean_object* v_months_945_){
_start:
{
lean_object* v_date_946_; lean_object* v_time_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_955_; 
v_date_946_ = lean_ctor_get(v_dt_944_, 0);
v_time_947_ = lean_ctor_get(v_dt_944_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_dt_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_949_ = v_dt_944_;
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_time_947_);
lean_inc(v_date_946_);
lean_dec(v_dt_944_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = l_Std_Time_PlainDate_addMonthsClip(v_date_946_, v_months_945_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_time_947_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_956_, lean_object* v_months_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_956_, v_months_957_);
lean_dec(v_months_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_959_, lean_object* v_months_960_){
_start:
{
lean_object* v_date_961_; lean_object* v_time_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v_date_961_ = lean_ctor_get(v_dt_959_, 0);
v_time_962_ = lean_ctor_get(v_dt_959_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_dt_959_);
if (v_isSharedCheck_971_ == 0)
{
v___x_964_ = v_dt_959_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_time_962_);
lean_inc(v_date_961_);
lean_dec(v_dt_959_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = lean_int_neg(v_months_960_);
v___x_967_ = l_Std_Time_PlainDate_addMonthsClip(v_date_961_, v___x_966_);
lean_dec(v___x_966_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_time_962_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_972_, lean_object* v_months_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_972_, v_months_973_);
lean_dec(v_months_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_975_, lean_object* v_months_976_){
_start:
{
lean_object* v_date_977_; lean_object* v_time_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_date_977_ = lean_ctor_get(v_dt_975_, 0);
v_time_978_ = lean_ctor_get(v_dt_975_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_dt_975_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v_dt_975_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_time_978_);
lean_inc(v_date_977_);
lean_dec(v_dt_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_977_, v_months_976_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_time_978_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_987_, lean_object* v_months_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_987_, v_months_988_);
lean_dec(v_months_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_990_, lean_object* v_months_991_){
_start:
{
lean_object* v_date_992_; lean_object* v_time_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
v_date_992_ = lean_ctor_get(v_dt_990_, 0);
v_time_993_ = lean_ctor_get(v_dt_990_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_dt_990_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v_dt_990_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_time_993_);
lean_inc(v_date_992_);
lean_dec(v_dt_990_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = lean_int_neg(v_months_991_);
v___x_998_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_992_, v___x_997_);
lean_dec(v___x_997_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_time_993_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_1003_, lean_object* v_months_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_1003_, v_months_1004_);
lean_dec(v_months_1004_);
return v_res_1005_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_unsigned_to_nat(12u);
v___x_1007_ = lean_nat_to_int(v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_1008_, lean_object* v_years_1009_){
_start:
{
lean_object* v_date_1010_; lean_object* v_time_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1021_; 
v_date_1010_ = lean_ctor_get(v_dt_1008_, 0);
v_time_1011_ = lean_ctor_get(v_dt_1008_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_dt_1008_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1013_ = v_dt_1008_;
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_time_1011_);
lean_inc(v_date_1010_);
lean_dec(v_dt_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1015_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1016_ = lean_int_mul(v_years_1009_, v___x_1015_);
v___x_1017_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1010_, v___x_1016_);
lean_dec(v___x_1016_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_time_1011_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_1022_, lean_object* v_years_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_1022_, v_years_1023_);
lean_dec(v_years_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_1025_, lean_object* v_years_1026_){
_start:
{
lean_object* v_date_1027_; lean_object* v_time_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v_date_1027_ = lean_ctor_get(v_dt_1025_, 0);
v_time_1028_ = lean_ctor_get(v_dt_1025_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_dt_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1030_ = v_dt_1025_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_time_1028_);
lean_inc(v_date_1027_);
lean_dec(v_dt_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1032_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1033_ = lean_int_mul(v_years_1026_, v___x_1032_);
v___x_1034_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1027_, v___x_1033_);
lean_dec(v___x_1033_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_time_1028_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_1039_, lean_object* v_years_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_1039_, v_years_1040_);
lean_dec(v_years_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_1042_, lean_object* v_years_1043_){
_start:
{
lean_object* v_date_1044_; lean_object* v_time_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1056_; 
v_date_1044_ = lean_ctor_get(v_dt_1042_, 0);
v_time_1045_ = lean_ctor_get(v_dt_1042_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_dt_1042_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1047_ = v_dt_1042_;
v_isShared_1048_ = v_isSharedCheck_1056_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_time_1045_);
lean_inc(v_date_1044_);
lean_dec(v_dt_1042_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1056_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1049_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1050_ = lean_int_mul(v_years_1043_, v___x_1049_);
v___x_1051_ = lean_int_neg(v___x_1050_);
lean_dec(v___x_1050_);
v___x_1052_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1044_, v___x_1051_);
lean_dec(v___x_1051_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1052_);
v___x_1054_ = v___x_1047_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_time_1045_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_1057_, lean_object* v_years_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_1057_, v_years_1058_);
lean_dec(v_years_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_1060_, lean_object* v_years_1061_){
_start:
{
lean_object* v_date_1062_; lean_object* v_time_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
v_date_1062_ = lean_ctor_get(v_dt_1060_, 0);
v_time_1063_ = lean_ctor_get(v_dt_1060_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_dt_1060_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1065_ = v_dt_1060_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_time_1063_);
lean_inc(v_date_1062_);
lean_dec(v_dt_1060_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1067_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1068_ = lean_int_mul(v_years_1061_, v___x_1067_);
v___x_1069_ = lean_int_neg(v___x_1068_);
lean_dec(v___x_1068_);
v___x_1070_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1062_, v___x_1069_);
lean_dec(v___x_1069_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1070_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_time_1063_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_1075_, lean_object* v_years_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_1075_, v_years_1076_);
lean_dec(v_years_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_1078_, lean_object* v_nanos_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v_second_1081_; lean_object* v_nano_1082_; lean_object* v___x_1083_; lean_object* v_second_1084_; lean_object* v_nano_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1080_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1078_);
v_second_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_second_1081_);
v_nano_1082_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_nano_1082_);
lean_dec_ref(v___x_1080_);
v___x_1083_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1079_);
v_second_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_second_1084_);
v_nano_1085_ = lean_ctor_get(v___x_1083_, 1);
lean_inc(v_nano_1085_);
lean_dec_ref(v___x_1083_);
v___x_1086_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1087_ = lean_int_mul(v_second_1081_, v___x_1086_);
lean_dec(v_second_1081_);
v___x_1088_ = lean_int_add(v___x_1087_, v_nano_1082_);
lean_dec(v_nano_1082_);
lean_dec(v___x_1087_);
v___x_1089_ = lean_int_mul(v_second_1084_, v___x_1086_);
lean_dec(v_second_1084_);
v___x_1090_ = lean_int_add(v___x_1089_, v_nano_1085_);
lean_dec(v_nano_1085_);
lean_dec(v___x_1089_);
v___x_1091_ = lean_int_add(v___x_1088_, v___x_1090_);
lean_dec(v___x_1090_);
lean_dec(v___x_1088_);
v___x_1092_ = l_Std_Time_Duration_ofNanoseconds(v___x_1091_);
lean_dec(v___x_1091_);
v___x_1093_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_1094_, lean_object* v_nanos_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_1094_, v_nanos_1095_);
lean_dec(v_nanos_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_1097_, lean_object* v_nanos_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v_second_1100_; lean_object* v_nano_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_second_1104_; lean_object* v_nano_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1099_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1097_);
v_second_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_second_1100_);
v_nano_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_nano_1101_);
lean_dec_ref(v___x_1099_);
v___x_1102_ = lean_int_neg(v_nanos_1098_);
v___x_1103_ = l_Std_Time_Duration_ofNanoseconds(v___x_1102_);
lean_dec(v___x_1102_);
v_second_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_second_1104_);
v_nano_1105_ = lean_ctor_get(v___x_1103_, 1);
lean_inc(v_nano_1105_);
lean_dec_ref(v___x_1103_);
v___x_1106_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1107_ = lean_int_mul(v_second_1100_, v___x_1106_);
lean_dec(v_second_1100_);
v___x_1108_ = lean_int_add(v___x_1107_, v_nano_1101_);
lean_dec(v_nano_1101_);
lean_dec(v___x_1107_);
v___x_1109_ = lean_int_mul(v_second_1104_, v___x_1106_);
lean_dec(v_second_1104_);
v___x_1110_ = lean_int_add(v___x_1109_, v_nano_1105_);
lean_dec(v_nano_1105_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_int_add(v___x_1108_, v___x_1110_);
lean_dec(v___x_1110_);
lean_dec(v___x_1108_);
v___x_1112_ = l_Std_Time_Duration_ofNanoseconds(v___x_1111_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_1114_, lean_object* v_nanos_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_1114_, v_nanos_1115_);
lean_dec(v_nanos_1115_);
return v_res_1116_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_cstr_to_nat("3600000000000");
v___x_1118_ = lean_nat_to_int(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_1119_, lean_object* v_hours_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v_second_1122_; lean_object* v_nano_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_second_1127_; lean_object* v_nano_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1121_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1119_);
v_second_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_second_1122_);
v_nano_1123_ = lean_ctor_get(v___x_1121_, 1);
lean_inc(v_nano_1123_);
lean_dec_ref(v___x_1121_);
v___x_1124_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1125_ = lean_int_mul(v_hours_1120_, v___x_1124_);
v___x_1126_ = l_Std_Time_Duration_ofNanoseconds(v___x_1125_);
lean_dec(v___x_1125_);
v_second_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_second_1127_);
v_nano_1128_ = lean_ctor_get(v___x_1126_, 1);
lean_inc(v_nano_1128_);
lean_dec_ref(v___x_1126_);
v___x_1129_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1130_ = lean_int_mul(v_second_1122_, v___x_1129_);
lean_dec(v_second_1122_);
v___x_1131_ = lean_int_add(v___x_1130_, v_nano_1123_);
lean_dec(v_nano_1123_);
lean_dec(v___x_1130_);
v___x_1132_ = lean_int_mul(v_second_1127_, v___x_1129_);
lean_dec(v_second_1127_);
v___x_1133_ = lean_int_add(v___x_1132_, v_nano_1128_);
lean_dec(v_nano_1128_);
lean_dec(v___x_1132_);
v___x_1134_ = lean_int_add(v___x_1131_, v___x_1133_);
lean_dec(v___x_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = l_Std_Time_Duration_ofNanoseconds(v___x_1134_);
lean_dec(v___x_1134_);
v___x_1136_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_1137_, lean_object* v_hours_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_Time_PlainDateTime_addHours(v_dt_1137_, v_hours_1138_);
lean_dec(v_hours_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_1140_, lean_object* v_hours_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v_second_1143_; lean_object* v_nano_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_second_1149_; lean_object* v_nano_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1142_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1140_);
v_second_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_second_1143_);
v_nano_1144_ = lean_ctor_get(v___x_1142_, 1);
lean_inc(v_nano_1144_);
lean_dec_ref(v___x_1142_);
v___x_1145_ = lean_int_neg(v_hours_1141_);
v___x_1146_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1147_ = lean_int_mul(v___x_1145_, v___x_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = l_Std_Time_Duration_ofNanoseconds(v___x_1147_);
lean_dec(v___x_1147_);
v_second_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_second_1149_);
v_nano_1150_ = lean_ctor_get(v___x_1148_, 1);
lean_inc(v_nano_1150_);
lean_dec_ref(v___x_1148_);
v___x_1151_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1152_ = lean_int_mul(v_second_1143_, v___x_1151_);
lean_dec(v_second_1143_);
v___x_1153_ = lean_int_add(v___x_1152_, v_nano_1144_);
lean_dec(v_nano_1144_);
lean_dec(v___x_1152_);
v___x_1154_ = lean_int_mul(v_second_1149_, v___x_1151_);
lean_dec(v_second_1149_);
v___x_1155_ = lean_int_add(v___x_1154_, v_nano_1150_);
lean_dec(v_nano_1150_);
lean_dec(v___x_1154_);
v___x_1156_ = lean_int_add(v___x_1153_, v___x_1155_);
lean_dec(v___x_1155_);
lean_dec(v___x_1153_);
v___x_1157_ = l_Std_Time_Duration_ofNanoseconds(v___x_1156_);
lean_dec(v___x_1156_);
v___x_1158_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_1159_, lean_object* v_hours_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_Time_PlainDateTime_subHours(v_dt_1159_, v_hours_1160_);
lean_dec(v_hours_1160_);
return v_res_1161_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_cstr_to_nat("60000000000");
v___x_1163_ = lean_nat_to_int(v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_1164_, lean_object* v_minutes_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v_second_1167_; lean_object* v_nano_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_second_1172_; lean_object* v_nano_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1166_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1164_);
v_second_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_second_1167_);
v_nano_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_nano_1168_);
lean_dec_ref(v___x_1166_);
v___x_1169_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1170_ = lean_int_mul(v_minutes_1165_, v___x_1169_);
v___x_1171_ = l_Std_Time_Duration_ofNanoseconds(v___x_1170_);
lean_dec(v___x_1170_);
v_second_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_second_1172_);
v_nano_1173_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_nano_1173_);
lean_dec_ref(v___x_1171_);
v___x_1174_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1175_ = lean_int_mul(v_second_1167_, v___x_1174_);
lean_dec(v_second_1167_);
v___x_1176_ = lean_int_add(v___x_1175_, v_nano_1168_);
lean_dec(v_nano_1168_);
lean_dec(v___x_1175_);
v___x_1177_ = lean_int_mul(v_second_1172_, v___x_1174_);
lean_dec(v_second_1172_);
v___x_1178_ = lean_int_add(v___x_1177_, v_nano_1173_);
lean_dec(v_nano_1173_);
lean_dec(v___x_1177_);
v___x_1179_ = lean_int_add(v___x_1176_, v___x_1178_);
lean_dec(v___x_1178_);
lean_dec(v___x_1176_);
v___x_1180_ = l_Std_Time_Duration_ofNanoseconds(v___x_1179_);
lean_dec(v___x_1179_);
v___x_1181_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_1182_, lean_object* v_minutes_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_1182_, v_minutes_1183_);
lean_dec(v_minutes_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_1185_, lean_object* v_minutes_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v_second_1188_; lean_object* v_nano_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_second_1194_; lean_object* v_nano_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1187_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1185_);
v_second_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_second_1188_);
v_nano_1189_ = lean_ctor_get(v___x_1187_, 1);
lean_inc(v_nano_1189_);
lean_dec_ref(v___x_1187_);
v___x_1190_ = lean_int_neg(v_minutes_1186_);
v___x_1191_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1192_ = lean_int_mul(v___x_1190_, v___x_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = l_Std_Time_Duration_ofNanoseconds(v___x_1192_);
lean_dec(v___x_1192_);
v_second_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_second_1194_);
v_nano_1195_ = lean_ctor_get(v___x_1193_, 1);
lean_inc(v_nano_1195_);
lean_dec_ref(v___x_1193_);
v___x_1196_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1197_ = lean_int_mul(v_second_1188_, v___x_1196_);
lean_dec(v_second_1188_);
v___x_1198_ = lean_int_add(v___x_1197_, v_nano_1189_);
lean_dec(v_nano_1189_);
lean_dec(v___x_1197_);
v___x_1199_ = lean_int_mul(v_second_1194_, v___x_1196_);
lean_dec(v_second_1194_);
v___x_1200_ = lean_int_add(v___x_1199_, v_nano_1195_);
lean_dec(v_nano_1195_);
lean_dec(v___x_1199_);
v___x_1201_ = lean_int_add(v___x_1198_, v___x_1200_);
lean_dec(v___x_1200_);
lean_dec(v___x_1198_);
v___x_1202_ = l_Std_Time_Duration_ofNanoseconds(v___x_1201_);
lean_dec(v___x_1201_);
v___x_1203_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_1204_, lean_object* v_minutes_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_1204_, v_minutes_1205_);
lean_dec(v_minutes_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_1207_, lean_object* v_seconds_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v_second_1210_; lean_object* v_nano_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_second_1215_; lean_object* v_nano_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1209_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1207_);
v_second_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_second_1210_);
v_nano_1211_ = lean_ctor_get(v___x_1209_, 1);
lean_inc(v_nano_1211_);
lean_dec_ref(v___x_1209_);
v___x_1212_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1213_ = lean_int_mul(v_seconds_1208_, v___x_1212_);
v___x_1214_ = l_Std_Time_Duration_ofNanoseconds(v___x_1213_);
lean_dec(v___x_1213_);
v_second_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_second_1215_);
v_nano_1216_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_nano_1216_);
lean_dec_ref(v___x_1214_);
v___x_1217_ = lean_int_mul(v_second_1210_, v___x_1212_);
lean_dec(v_second_1210_);
v___x_1218_ = lean_int_add(v___x_1217_, v_nano_1211_);
lean_dec(v_nano_1211_);
lean_dec(v___x_1217_);
v___x_1219_ = lean_int_mul(v_second_1215_, v___x_1212_);
lean_dec(v_second_1215_);
v___x_1220_ = lean_int_add(v___x_1219_, v_nano_1216_);
lean_dec(v_nano_1216_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_int_add(v___x_1218_, v___x_1220_);
lean_dec(v___x_1220_);
lean_dec(v___x_1218_);
v___x_1222_ = l_Std_Time_Duration_ofNanoseconds(v___x_1221_);
lean_dec(v___x_1221_);
v___x_1223_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_1224_, lean_object* v_seconds_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_1224_, v_seconds_1225_);
lean_dec(v_seconds_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_1227_, lean_object* v_seconds_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v_second_1230_; lean_object* v_nano_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_second_1236_; lean_object* v_nano_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1229_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1227_);
v_second_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_second_1230_);
v_nano_1231_ = lean_ctor_get(v___x_1229_, 1);
lean_inc(v_nano_1231_);
lean_dec_ref(v___x_1229_);
v___x_1232_ = lean_int_neg(v_seconds_1228_);
v___x_1233_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1234_ = lean_int_mul(v___x_1232_, v___x_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = l_Std_Time_Duration_ofNanoseconds(v___x_1234_);
lean_dec(v___x_1234_);
v_second_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_second_1236_);
v_nano_1237_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_nano_1237_);
lean_dec_ref(v___x_1235_);
v___x_1238_ = lean_int_mul(v_second_1230_, v___x_1233_);
lean_dec(v_second_1230_);
v___x_1239_ = lean_int_add(v___x_1238_, v_nano_1231_);
lean_dec(v_nano_1231_);
lean_dec(v___x_1238_);
v___x_1240_ = lean_int_mul(v_second_1236_, v___x_1233_);
lean_dec(v_second_1236_);
v___x_1241_ = lean_int_add(v___x_1240_, v_nano_1237_);
lean_dec(v_nano_1237_);
lean_dec(v___x_1240_);
v___x_1242_ = lean_int_add(v___x_1239_, v___x_1241_);
lean_dec(v___x_1241_);
lean_dec(v___x_1239_);
v___x_1243_ = l_Std_Time_Duration_ofNanoseconds(v___x_1242_);
lean_dec(v___x_1242_);
v___x_1244_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_1245_, lean_object* v_seconds_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_1245_, v_seconds_1246_);
lean_dec(v_seconds_1246_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_1248_, lean_object* v_milliseconds_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v_second_1251_; lean_object* v_nano_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_second_1256_; lean_object* v_nano_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1250_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1248_);
v_second_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_second_1251_);
v_nano_1252_ = lean_ctor_get(v___x_1250_, 1);
lean_inc(v_nano_1252_);
lean_dec_ref(v___x_1250_);
v___x_1253_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1254_ = lean_int_mul(v_milliseconds_1249_, v___x_1253_);
v___x_1255_ = l_Std_Time_Duration_ofNanoseconds(v___x_1254_);
lean_dec(v___x_1254_);
v_second_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_second_1256_);
v_nano_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_nano_1257_);
lean_dec_ref(v___x_1255_);
v___x_1258_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1259_ = lean_int_mul(v_second_1251_, v___x_1258_);
lean_dec(v_second_1251_);
v___x_1260_ = lean_int_add(v___x_1259_, v_nano_1252_);
lean_dec(v_nano_1252_);
lean_dec(v___x_1259_);
v___x_1261_ = lean_int_mul(v_second_1256_, v___x_1258_);
lean_dec(v_second_1256_);
v___x_1262_ = lean_int_add(v___x_1261_, v_nano_1257_);
lean_dec(v_nano_1257_);
lean_dec(v___x_1261_);
v___x_1263_ = lean_int_add(v___x_1260_, v___x_1262_);
lean_dec(v___x_1262_);
lean_dec(v___x_1260_);
v___x_1264_ = l_Std_Time_Duration_ofNanoseconds(v___x_1263_);
lean_dec(v___x_1263_);
v___x_1265_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_1266_, lean_object* v_milliseconds_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_1266_, v_milliseconds_1267_);
lean_dec(v_milliseconds_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_1269_, lean_object* v_milliseconds_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v_second_1272_; lean_object* v_nano_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_second_1278_; lean_object* v_nano_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1271_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_dt_1269_);
v_second_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_second_1272_);
v_nano_1273_ = lean_ctor_get(v___x_1271_, 1);
lean_inc(v_nano_1273_);
lean_dec_ref(v___x_1271_);
v___x_1274_ = lean_int_neg(v_milliseconds_1270_);
v___x_1275_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1276_ = lean_int_mul(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = l_Std_Time_Duration_ofNanoseconds(v___x_1276_);
lean_dec(v___x_1276_);
v_second_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_second_1278_);
v_nano_1279_ = lean_ctor_get(v___x_1277_, 1);
lean_inc(v_nano_1279_);
lean_dec_ref(v___x_1277_);
v___x_1280_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1281_ = lean_int_mul(v_second_1272_, v___x_1280_);
lean_dec(v_second_1272_);
v___x_1282_ = lean_int_add(v___x_1281_, v_nano_1273_);
lean_dec(v_nano_1273_);
lean_dec(v___x_1281_);
v___x_1283_ = lean_int_mul(v_second_1278_, v___x_1280_);
lean_dec(v_second_1278_);
v___x_1284_ = lean_int_add(v___x_1283_, v_nano_1279_);
lean_dec(v_nano_1279_);
lean_dec(v___x_1283_);
v___x_1285_ = lean_int_add(v___x_1282_, v___x_1284_);
lean_dec(v___x_1284_);
lean_dec(v___x_1282_);
v___x_1286_ = l_Std_Time_Duration_ofNanoseconds(v___x_1285_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1288_, lean_object* v_milliseconds_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1288_, v_milliseconds_1289_);
lean_dec(v_milliseconds_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1291_){
_start:
{
lean_object* v_date_1292_; lean_object* v_year_1293_; 
v_date_1292_ = lean_ctor_get(v_dt_1291_, 0);
v_year_1293_ = lean_ctor_get(v_date_1292_, 0);
lean_inc(v_year_1293_);
return v_year_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_Time_PlainDateTime_year(v_dt_1294_);
lean_dec_ref(v_dt_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1296_){
_start:
{
lean_object* v_date_1297_; lean_object* v_month_1298_; 
v_date_1297_ = lean_ctor_get(v_dt_1296_, 0);
v_month_1298_ = lean_ctor_get(v_date_1297_, 1);
lean_inc(v_month_1298_);
return v_month_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_Time_PlainDateTime_month(v_dt_1299_);
lean_dec_ref(v_dt_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1301_){
_start:
{
lean_object* v_date_1302_; lean_object* v_day_1303_; 
v_date_1302_ = lean_ctor_get(v_dt_1301_, 0);
v_day_1303_ = lean_ctor_get(v_date_1302_, 2);
lean_inc(v_day_1303_);
return v_day_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_Time_PlainDateTime_day(v_dt_1304_);
lean_dec_ref(v_dt_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1306_){
_start:
{
lean_object* v_date_1307_; uint8_t v___x_1308_; 
v_date_1307_ = lean_ctor_get(v_dt_1306_, 0);
lean_inc_ref(v_date_1307_);
lean_dec_ref(v_dt_1306_);
v___x_1308_ = l_Std_Time_PlainDate_weekday(v_date_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1309_){
_start:
{
uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_res_1310_ = l_Std_Time_PlainDateTime_weekday(v_dt_1309_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1312_){
_start:
{
lean_object* v_time_1313_; lean_object* v_hour_1314_; 
v_time_1313_ = lean_ctor_get(v_dt_1312_, 1);
v_hour_1314_ = lean_ctor_get(v_time_1313_, 0);
lean_inc(v_hour_1314_);
return v_hour_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_Time_PlainDateTime_hour(v_dt_1315_);
lean_dec_ref(v_dt_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1317_){
_start:
{
lean_object* v_time_1318_; lean_object* v_minute_1319_; 
v_time_1318_ = lean_ctor_get(v_dt_1317_, 1);
v_minute_1319_ = lean_ctor_get(v_time_1318_, 1);
lean_inc(v_minute_1319_);
return v_minute_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_Time_PlainDateTime_minute(v_dt_1320_);
lean_dec_ref(v_dt_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1322_){
_start:
{
lean_object* v_time_1323_; lean_object* v_nanosecond_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_time_1323_ = lean_ctor_get(v_dt_1322_, 1);
v_nanosecond_1324_ = lean_ctor_get(v_time_1323_, 3);
v___x_1325_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1326_ = lean_int_ediv(v_nanosecond_1324_, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1327_);
lean_dec_ref(v_dt_1327_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1329_){
_start:
{
lean_object* v_time_1330_; lean_object* v_second_1331_; 
v_time_1330_ = lean_ctor_get(v_dt_1329_, 1);
v_second_1331_ = lean_ctor_get(v_time_1330_, 2);
lean_inc(v_second_1331_);
return v_second_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_Time_PlainDateTime_second(v_dt_1332_);
lean_dec_ref(v_dt_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1334_){
_start:
{
lean_object* v_time_1335_; lean_object* v_nanosecond_1336_; 
v_time_1335_ = lean_ctor_get(v_dt_1334_, 1);
v_nanosecond_1336_ = lean_ctor_get(v_time_1335_, 3);
lean_inc(v_nanosecond_1336_);
return v_nanosecond_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1337_);
lean_dec_ref(v_dt_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1339_){
_start:
{
lean_object* v_date_1340_; lean_object* v_year_1341_; uint8_t v___x_1342_; 
v_date_1340_ = lean_ctor_get(v_date_1339_, 0);
v_year_1341_ = lean_ctor_get(v_date_1340_, 0);
v___x_1342_ = l_Std_Time_Year_Offset_era(v_year_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Std_Time_PlainDateTime_era(v_date_1343_);
lean_dec_ref(v_date_1343_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1346_){
_start:
{
lean_object* v_date_1347_; lean_object* v_year_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1356_; 
v_date_1347_ = lean_ctor_get(v_date_1346_, 0);
v_year_1348_ = lean_ctor_get(v_date_1347_, 0);
v___x_1349_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_1350_ = lean_int_mod(v_year_1348_, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1356_ = lean_int_dec_eq(v___x_1350_, v___x_1351_);
lean_dec(v___x_1350_);
if (v___x_1356_ == 0)
{
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v___x_1358_ = lean_int_mod(v_year_1348_, v___x_1357_);
v___x_1359_ = lean_int_dec_eq(v___x_1358_, v___x_1351_);
lean_dec(v___x_1358_);
if (v___x_1359_ == 0)
{
if (v___x_1356_ == 0)
{
goto v___jp_1352_;
}
else
{
return v___x_1356_;
}
}
else
{
goto v___jp_1352_;
}
}
v___jp_1352_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v___x_1354_ = lean_int_mod(v_year_1348_, v___x_1353_);
v___x_1355_ = lean_int_dec_eq(v___x_1354_, v___x_1351_);
lean_dec(v___x_1354_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object* v_date_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1360_);
lean_dec_ref(v_date_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1363_){
_start:
{
lean_object* v_date_1364_; lean_object* v___x_1365_; 
v_date_1364_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1364_);
lean_dec_ref(v_date_1363_);
v___x_1365_ = l_Std_Time_PlainDate_weekOfYear(v_date_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1366_){
_start:
{
lean_object* v_date_1367_; lean_object* v___x_1368_; 
v_date_1367_ = lean_ctor_get(v_date_1366_, 0);
v___x_1368_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1369_);
lean_dec_ref(v_date_1369_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1371_){
_start:
{
lean_object* v_date_1372_; lean_object* v___x_1373_; 
v_date_1372_ = lean_ctor_get(v_date_1371_, 0);
lean_inc_ref(v_date_1372_);
lean_dec_ref(v_date_1371_);
v___x_1373_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1374_){
_start:
{
lean_object* v_date_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1399_; 
v_date_1375_ = lean_ctor_get(v_date_1374_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_date_1374_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_date_1374_, 1);
lean_dec(v_unused_1400_);
v___x_1377_ = v_date_1374_;
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_date_1375_);
lean_dec(v_date_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_year_1379_; lean_object* v_month_1380_; lean_object* v_day_1381_; uint8_t v___y_1383_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1395_; 
v_year_1379_ = lean_ctor_get(v_date_1375_, 0);
lean_inc(v_year_1379_);
v_month_1380_ = lean_ctor_get(v_date_1375_, 1);
lean_inc(v_month_1380_);
v_day_1381_ = lean_ctor_get(v_date_1375_, 2);
lean_inc(v_day_1381_);
lean_dec_ref(v_date_1375_);
v___x_1388_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__10);
v___x_1389_ = lean_int_mod(v_year_1379_, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1395_ = lean_int_dec_eq(v___x_1389_, v___x_1390_);
lean_dec(v___x_1389_);
if (v___x_1395_ == 0)
{
lean_dec(v_year_1379_);
v___y_1383_ = v___x_1395_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__6);
v___x_1397_ = lean_int_mod(v_year_1379_, v___x_1396_);
v___x_1398_ = lean_int_dec_eq(v___x_1397_, v___x_1390_);
lean_dec(v___x_1397_);
if (v___x_1398_ == 0)
{
if (v___x_1395_ == 0)
{
goto v___jp_1391_;
}
else
{
lean_dec(v_year_1379_);
v___y_1383_ = v___x_1395_;
goto v___jp_1382_;
}
}
else
{
goto v___jp_1391_;
}
}
v___jp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v_day_1381_);
lean_ctor_set(v___x_1377_, 0, v_month_1380_);
v___x_1385_ = v___x_1377_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_month_1380_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_day_1381_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Std_Time_ValidDate_dayOfYear(v___y_1383_, v___x_1385_);
lean_dec_ref(v___x_1385_);
return v___x_1386_;
}
}
v___jp_1391_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2, &l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2_once, _init_l_Std_Time_PlainDateTime_ofTimestampAssumingUTC___closed__2);
v___x_1393_ = lean_int_mod(v_year_1379_, v___x_1392_);
lean_dec(v_year_1379_);
v___x_1394_ = lean_int_dec_eq(v___x_1393_, v___x_1390_);
lean_dec(v___x_1393_);
v___y_1383_ = v___x_1394_;
goto v___jp_1382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object* v_date_1401_){
_start:
{
lean_object* v_date_1402_; lean_object* v___x_1403_; 
v_date_1402_ = lean_ctor_get(v_date_1401_, 0);
v___x_1403_ = l_Std_Time_PlainDate_quarter(v_date_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object* v_date_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_Time_PlainDateTime_quarter(v_date_1404_);
lean_dec_ref(v_date_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object* v_date_1406_, lean_object* v_time_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_date_1406_);
lean_ctor_set(v___x_1408_, 1, v_time_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object* v_time_1409_, lean_object* v_date_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_date_1410_);
lean_ctor_set(v___x_1411_, 1, v_time_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object* v_x_1440_, lean_object* v_y_1441_){
_start:
{
lean_object* v_second_1442_; lean_object* v_nano_1443_; lean_object* v___x_1444_; lean_object* v_second_1445_; lean_object* v_nano_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_nanos_1449_; lean_object* v___x_1450_; lean_object* v_second_1451_; lean_object* v_nano_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_second_1442_ = lean_ctor_get(v_y_1441_, 0);
v_nano_1443_ = lean_ctor_get(v_y_1441_, 1);
v___x_1444_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_x_1440_);
v_second_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_second_1445_);
v_nano_1446_ = lean_ctor_get(v___x_1444_, 1);
lean_inc(v_nano_1446_);
lean_dec_ref(v___x_1444_);
v___x_1447_ = lean_obj_once(&l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1, &l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1_once, _init_l_Std_Time_PlainDateTime_toTimestampAssumingUTC___closed__1);
v___x_1448_ = lean_int_mul(v_second_1442_, v___x_1447_);
v_nanos_1449_ = lean_int_add(v___x_1448_, v_nano_1443_);
lean_dec(v___x_1448_);
v___x_1450_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1449_);
lean_dec(v_nanos_1449_);
v_second_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_second_1451_);
v_nano_1452_ = lean_ctor_get(v___x_1450_, 1);
lean_inc(v_nano_1452_);
lean_dec_ref(v___x_1450_);
v___x_1453_ = lean_int_mul(v_second_1445_, v___x_1447_);
lean_dec(v_second_1445_);
v___x_1454_ = lean_int_add(v___x_1453_, v_nano_1446_);
lean_dec(v_nano_1446_);
lean_dec(v___x_1453_);
v___x_1455_ = lean_int_mul(v_second_1451_, v___x_1447_);
lean_dec(v_second_1451_);
v___x_1456_ = lean_int_add(v___x_1455_, v_nano_1452_);
lean_dec(v_nano_1452_);
lean_dec(v___x_1455_);
v___x_1457_ = lean_int_add(v___x_1454_, v___x_1456_);
lean_dec(v___x_1456_);
lean_dec(v___x_1454_);
v___x_1458_ = l_Std_Time_Duration_ofNanoseconds(v___x_1457_);
lean_dec(v___x_1457_);
v___x_1459_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1460_, lean_object* v_y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_1460_, v_y_1461_);
lean_dec_ref(v_y_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object* v_date_1465_, lean_object* v_time_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_date_1465_);
lean_ctor_set(v___x_1467_, 1, v_time_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object* v_time_1468_, lean_object* v_date_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_date_1469_);
lean_ctor_set(v___x_1470_, 1, v_time_1468_);
return v___x_1470_;
}
}
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
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
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime_Timestamp(builtin);
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
