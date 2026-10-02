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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
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
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Fin_succ___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
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
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_withWeekday(lean_object*, uint8_t);
lean_object* l_Std_Time_instReprPlainDate_repr___redArg(lean_object*);
lean_object* l_Std_Time_instReprPlainTime_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Std_Time_instDecidableEqPlainDate_decEq(lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqPlainTime_decEq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__1;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__2;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__3;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__4;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__5;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__6;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__7;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__8;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__9;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__10;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__11;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__12;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__13;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__14;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__15;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__16;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__17;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__18;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__19;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__20;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__21;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__22;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__23;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__24;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__25;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__26;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__27;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__28;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__29;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__30;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__31;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(lean_object* v_as_x27_254_, lean_object* v_b_255_){
_start:
{
if (lean_obj_tag(v_as_x27_254_) == 0)
{
return v_b_255_;
}
else
{
lean_object* v_head_256_; lean_object* v_tail_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_275_; 
v_head_256_ = lean_ctor_get(v_as_x27_254_, 0);
v_tail_257_ = lean_ctor_get(v_as_x27_254_, 1);
v_fst_258_ = lean_ctor_get(v_b_255_, 0);
v_snd_259_ = lean_ctor_get(v_b_255_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_b_255_);
if (v_isSharedCheck_275_ == 0)
{
v___x_261_ = v_b_255_;
v_isShared_262_ = v_isSharedCheck_275_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snd_259_);
lean_inc(v_fst_258_);
lean_dec(v_b_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_275_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_263_ = lean_unsigned_to_nat(13u);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Fin_add(v___x_263_, v_snd_259_, v___x_264_);
lean_dec(v_snd_259_);
v___x_266_ = lean_int_dec_lt(v_fst_258_, v_head_256_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_int_sub(v_fst_258_, v_head_256_);
lean_dec(v_fst_258_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_265_);
lean_ctor_set(v___x_261_, 0, v___x_267_);
v___x_269_ = v___x_261_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_265_);
v___x_269_ = v_reuseFailAlloc_271_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
v_as_x27_254_ = v_tail_257_;
v_b_255_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v___x_273_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_265_);
v___x_273_ = v___x_261_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_fst_258_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_265_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___boxed(lean_object* v_as_x27_276_, lean_object* v_b_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_276_, v_b_277_);
lean_dec(v_as_x27_276_);
return v_res_278_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v_leapYearEpoch_280_; 
v___x_279_ = lean_unsigned_to_nat(11017u);
v_leapYearEpoch_280_ = lean_nat_to_int(v___x_279_);
return v_leapYearEpoch_280_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(365u);
v___x_282_ = lean_nat_to_int(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(400u);
v___x_284_ = lean_nat_to_int(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_286_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_287_ = lean_int_mul(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(97u);
v___x_289_ = lean_nat_to_int(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_daysPer400Y_292_; 
v___x_290_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__4, &l_Std_Time_PlainDateTime_ofWallTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4);
v___x_291_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__3, &l_Std_Time_PlainDateTime_ofWallTime___closed__3_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3);
v_daysPer400Y_292_ = lean_int_add(v___x_291_, v___x_290_);
return v_daysPer400Y_292_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(100u);
v___x_294_ = lean_nat_to_int(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_296_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_297_ = lean_int_mul(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(24u);
v___x_299_ = lean_nat_to_int(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_daysPer100Y_302_; 
v___x_300_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__8, &l_Std_Time_PlainDateTime_ofWallTime___closed__8_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8);
v___x_301_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__7, &l_Std_Time_PlainDateTime_ofWallTime___closed__7_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7);
v_daysPer100Y_302_ = lean_int_add(v___x_301_, v___x_300_);
return v_daysPer100Y_302_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(4u);
v___x_304_ = lean_nat_to_int(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_306_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_307_ = lean_int_mul(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_daysPer4Y_310_; 
v___x_308_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_309_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__11, &l_Std_Time_PlainDateTime_ofWallTime___closed__11_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11);
v_daysPer4Y_310_ = lean_int_add(v___x_309_, v___x_308_);
return v_daysPer4Y_310_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(60u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(3600u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(31u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(29u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
v___x_320_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__16, &l_Std_Time_PlainDateTime_ofWallTime___closed__16_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16);
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__17, &l_Std_Time_PlainDateTime_ofWallTime___closed__17_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17);
v___x_323_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__18, &l_Std_Time_PlainDateTime_ofWallTime___closed__18_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18);
v___x_326_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__19, &l_Std_Time_PlainDateTime_ofWallTime___closed__19_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19);
v___x_329_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__20, &l_Std_Time_PlainDateTime_ofWallTime___closed__20_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20);
v___x_332_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__21, &l_Std_Time_PlainDateTime_ofWallTime___closed__21_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21);
v___x_335_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__22, &l_Std_Time_PlainDateTime_ofWallTime___closed__22_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22);
v___x_338_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__23, &l_Std_Time_PlainDateTime_ofWallTime___closed__23_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23);
v___x_341_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__24, &l_Std_Time_PlainDateTime_ofWallTime___closed__24_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24);
v___x_344_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__25, &l_Std_Time_PlainDateTime_ofWallTime___closed__25_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25);
v___x_347_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__26, &l_Std_Time_PlainDateTime_ofWallTime___closed__26_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26);
v___x_350_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_months_354_; 
v___x_352_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__27, &l_Std_Time_PlainDateTime_ofWallTime___closed__27_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27);
v___x_353_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v_months_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_months_354_, 0, v___x_353_);
lean_ctor_set(v_months_354_, 1, v___x_352_);
return v_months_354_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(2000u);
v___x_356_ = lean_nat_to_int(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(25u);
v___x_358_ = lean_nat_to_int(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_360_ = lean_int_neg(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object* v_stamp_361_){
_start:
{
lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; uint8_t v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; uint8_t v___y_392_; lean_object* v_second_393_; lean_object* v_nano_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_533_; 
v_second_393_ = lean_ctor_get(v_stamp_361_, 0);
v_nano_394_ = lean_ctor_get(v_stamp_361_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_stamp_361_);
if (v_isSharedCheck_533_ == 0)
{
v___x_396_ = v_stamp_361_;
v_isShared_397_ = v_isSharedCheck_533_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_nano_394_);
lean_inc(v_second_393_);
lean_dec(v_stamp_361_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_533_;
goto v_resetjp_395_;
}
v___jp_362_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v___y_364_);
lean_ctor_set(v___x_368_, 1, v___y_366_);
lean_ctor_set(v___x_368_, 2, v___y_363_);
lean_ctor_set(v___x_368_, 3, v___y_365_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___y_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
v___jp_370_:
{
lean_object* v_max_379_; uint8_t v___x_380_; 
v_max_379_ = l_Std_Time_Month_Ordinal_days(v___y_378_, v___y_373_);
v___x_380_ = lean_int_dec_lt(v_max_379_, v___y_374_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_max_379_);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v___y_375_);
lean_ctor_set(v___x_381_, 1, v___y_373_);
lean_ctor_set(v___x_381_, 2, v___y_374_);
v___y_363_ = v___y_371_;
v___y_364_ = v___y_372_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_376_;
v___y_367_ = v___x_381_;
goto v___jp_362_;
}
else
{
lean_object* v___x_382_; 
lean_dec(v___y_374_);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v___y_375_);
lean_ctor_set(v___x_382_, 1, v___y_373_);
lean_ctor_set(v___x_382_, 2, v_max_379_);
v___y_363_ = v___y_371_;
v___y_364_ = v___y_372_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_376_;
v___y_367_ = v___x_382_;
goto v___jp_362_;
}
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
v___y_371_ = v___y_385_;
v___y_372_ = v___y_386_;
v___y_373_ = v___y_387_;
v___y_374_ = v___y_388_;
v___y_375_ = v___y_389_;
v___y_376_ = v___y_391_;
v___y_377_ = v___y_390_;
v___y_378_ = v___y_384_;
goto v___jp_370_;
}
else
{
v___y_371_ = v___y_385_;
v___y_372_ = v___y_386_;
v___y_373_ = v___y_387_;
v___y_374_ = v___y_388_;
v___y_375_ = v___y_389_;
v___y_376_ = v___y_391_;
v___y_377_ = v___y_390_;
v___y_378_ = v___y_392_;
goto v___jp_370_;
}
}
v_resetjp_395_:
{
lean_object* v_leapYearEpoch_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_daysPer400Y_401_; lean_object* v___x_402_; lean_object* v_daysPer100Y_403_; lean_object* v___x_404_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_daysPer4Y_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v_hmon_432_; lean_object* v_year_433_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_remYears_450_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v_quadrennialCycles_485_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_centenialCycles_495_; lean_object* v___y_503_; lean_object* v_quadracentennialCycles_504_; lean_object* v_remDays_505_; lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v_snd_519_; lean_object* v_secs_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_leapYearEpoch_398_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__0, &l_Std_Time_PlainDateTime_ofWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0);
v___x_399_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_400_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v_daysPer400Y_401_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__5, &l_Std_Time_PlainDateTime_ofWallTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5);
v___x_402_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v_daysPer100Y_403_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__9, &l_Std_Time_PlainDateTime_ofWallTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9);
v___x_404_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v_daysPer4Y_424_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__12, &l_Std_Time_PlainDateTime_ofWallTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12);
v___x_425_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_426_ = lean_int_mul(v_second_393_, v___x_425_);
lean_dec(v_second_393_);
v___x_427_ = lean_int_add(v___x_426_, v_nano_394_);
lean_dec(v_nano_394_);
lean_dec(v___x_426_);
v_secs_528_ = lean_int_div(v___x_427_, v___x_425_);
v___x_529_ = lean_int_mod(v___x_427_, v___x_425_);
v___x_530_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_531_ = lean_int_dec_lt(v___x_529_, v___x_530_);
lean_dec(v___x_529_);
if (v___x_531_ == 0)
{
v_snd_519_ = v_secs_528_;
goto v___jp_518_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_int_sub(v_secs_528_, v___x_423_);
lean_dec(v_secs_528_);
v_snd_519_ = v___x_532_;
goto v___jp_518_;
}
v___jp_405_:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_414_ = lean_int_mod(v___y_409_, v___x_404_);
v___x_415_ = lean_nat_to_int(v___y_412_);
v___x_416_ = lean_int_dec_eq(v___x_414_, v___x_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_int_mod(v___y_409_, v___x_402_);
v___x_418_ = lean_int_dec_eq(v___x_417_, v___x_415_);
lean_dec(v___x_417_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; 
lean_dec(v___x_415_);
v___x_419_ = 1;
v___y_384_ = v___x_416_;
v___y_385_ = v___y_406_;
v___y_386_ = v___y_407_;
v___y_387_ = v___y_408_;
v___y_388_ = v___y_413_;
v___y_389_ = v___y_409_;
v___y_390_ = v___y_410_;
v___y_391_ = v___y_411_;
v___y_392_ = v___x_419_;
goto v___jp_383_;
}
else
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_int_mod(v___y_409_, v___x_400_);
v___x_421_ = lean_int_dec_eq(v___x_420_, v___x_415_);
lean_dec(v___x_415_);
lean_dec(v___x_420_);
v___y_384_ = v___x_416_;
v___y_385_ = v___y_406_;
v___y_386_ = v___y_407_;
v___y_387_ = v___y_408_;
v___y_388_ = v___y_413_;
v___y_389_ = v___y_409_;
v___y_390_ = v___y_410_;
v___y_391_ = v___y_411_;
v___y_392_ = v___x_421_;
goto v___jp_383_;
}
}
v___jp_428_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_434_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__13, &l_Std_Time_PlainDateTime_ofWallTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13);
v___x_435_ = lean_int_emod(v___y_429_, v___x_434_);
v___x_436_ = lean_int_ediv(v___y_429_, v___x_434_);
v___x_437_ = lean_int_emod(v___x_436_, v___x_434_);
lean_dec(v___x_436_);
v___x_438_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__14, &l_Std_Time_PlainDateTime_ofWallTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14);
v___x_439_ = lean_int_ediv(v___y_429_, v___x_438_);
lean_dec(v___y_429_);
v___x_440_ = lean_int_emod(v___x_427_, v___x_425_);
lean_dec(v___x_427_);
v___x_441_ = l_Fin_succ___redArg(v___y_430_);
lean_dec(v___y_430_);
v___x_442_ = lean_nat_dec_le(v___x_422_, v___x_441_);
if (v___x_442_ == 0)
{
lean_dec(v___x_441_);
v___y_406_ = v___x_435_;
v___y_407_ = v___x_439_;
v___y_408_ = v_hmon_432_;
v___y_409_ = v_year_433_;
v___y_410_ = v___x_440_;
v___y_411_ = v___x_437_;
v___y_412_ = v___y_431_;
v___y_413_ = v___x_423_;
goto v___jp_405_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_nat_to_int(v___x_441_);
v___y_406_ = v___x_435_;
v___y_407_ = v___x_439_;
v___y_408_ = v_hmon_432_;
v___y_409_ = v_year_433_;
v___y_410_ = v___x_440_;
v___y_411_ = v___x_437_;
v___y_412_ = v___y_431_;
v___y_413_ = v___x_443_;
goto v___jp_405_;
}
}
v___jp_444_:
{
lean_object* v___x_451_; lean_object* v_remDays_452_; lean_object* v___x_453_; lean_object* v_months_454_; lean_object* v_mon_455_; lean_object* v___x_457_; 
v___x_451_ = lean_int_mul(v_remYears_450_, v___x_399_);
v_remDays_452_ = lean_int_sub(v___y_448_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___y_448_);
v___x_453_ = lean_unsigned_to_nat(31u);
v_months_454_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__28, &l_Std_Time_PlainDateTime_ofWallTime___closed__28_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28);
v_mon_455_ = lean_unsigned_to_nat(0u);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v_mon_455_);
lean_ctor_set(v___x_396_, 0, v_remDays_452_);
v___x_457_ = v___x_396_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_remDays_452_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_mon_455_);
v___x_457_ = v_reuseFailAlloc_479_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_year_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_458_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_months_454_, v___x_457_);
v_fst_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_fst_459_);
v_snd_460_ = lean_ctor_get(v___x_458_, 1);
lean_inc(v_snd_460_);
lean_dec_ref(v___x_458_);
v___x_461_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__29, &l_Std_Time_PlainDateTime_ofWallTime___closed__29_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29);
v___x_462_ = lean_int_add(v___x_461_, v_remYears_450_);
lean_dec(v_remYears_450_);
v___x_463_ = lean_int_mul(v___x_404_, v___y_449_);
lean_dec(v___y_449_);
v___x_464_ = lean_int_add(v___x_462_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_int_mul(v___x_402_, v___y_447_);
lean_dec(v___y_447_);
v___x_466_ = lean_int_add(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_int_mul(v___x_400_, v___y_445_);
lean_dec(v___y_445_);
v_year_468_ = lean_int_add(v___x_466_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_466_);
v___x_469_ = l_Int_toNat(v_fst_459_);
lean_dec(v_fst_459_);
v___x_470_ = lean_nat_mod(v___x_469_, v___x_453_);
lean_dec(v___x_469_);
v___x_471_ = lean_unsigned_to_nat(10u);
v___x_472_ = lean_nat_dec_lt(v___x_471_, v_snd_460_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_unsigned_to_nat(2u);
v___x_474_ = lean_nat_add(v_snd_460_, v___x_473_);
lean_dec(v_snd_460_);
v___x_475_ = lean_nat_to_int(v___x_474_);
v___y_429_ = v___y_446_;
v___y_430_ = v___x_470_;
v___y_431_ = v_mon_455_;
v_hmon_432_ = v___x_475_;
v_year_433_ = v_year_468_;
goto v___jp_428_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_int_add(v_year_468_, v___x_423_);
lean_dec(v_year_468_);
v___x_477_ = lean_nat_sub(v_snd_460_, v___x_471_);
lean_dec(v_snd_460_);
v___x_478_ = lean_nat_to_int(v___x_477_);
v___y_429_ = v___y_446_;
v___y_430_ = v___x_470_;
v___y_431_ = v_mon_455_;
v_hmon_432_ = v___x_478_;
v_year_433_ = v___x_476_;
goto v___jp_428_;
}
}
}
v___jp_480_:
{
lean_object* v___x_486_; lean_object* v_remDays_487_; lean_object* v_remYears_488_; uint8_t v___x_489_; 
v___x_486_ = lean_int_mul(v_quadrennialCycles_485_, v_daysPer4Y_424_);
v_remDays_487_ = lean_int_sub(v___y_484_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v___y_484_);
v_remYears_488_ = lean_int_ediv(v_remDays_487_, v___x_399_);
v___x_489_ = lean_int_dec_eq(v_remYears_488_, v___x_404_);
if (v___x_489_ == 0)
{
v___y_445_ = v___y_481_;
v___y_446_ = v___y_482_;
v___y_447_ = v___y_483_;
v___y_448_ = v_remDays_487_;
v___y_449_ = v_quadrennialCycles_485_;
v_remYears_450_ = v_remYears_488_;
goto v___jp_444_;
}
else
{
lean_object* v_remYears_490_; 
v_remYears_490_ = lean_int_sub(v_remYears_488_, v___x_423_);
lean_dec(v_remYears_488_);
v___y_445_ = v___y_481_;
v___y_446_ = v___y_482_;
v___y_447_ = v___y_483_;
v___y_448_ = v_remDays_487_;
v___y_449_ = v_quadrennialCycles_485_;
v_remYears_450_ = v_remYears_490_;
goto v___jp_444_;
}
}
v___jp_491_:
{
lean_object* v___x_496_; lean_object* v_remDays_497_; lean_object* v_quadrennialCycles_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_496_ = lean_int_mul(v_centenialCycles_495_, v_daysPer100Y_403_);
v_remDays_497_ = lean_int_sub(v___y_494_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v___y_494_);
v_quadrennialCycles_498_ = lean_int_ediv(v_remDays_497_, v_daysPer4Y_424_);
v___x_499_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__30, &l_Std_Time_PlainDateTime_ofWallTime___closed__30_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30);
v___x_500_ = lean_int_dec_eq(v_quadrennialCycles_498_, v___x_499_);
if (v___x_500_ == 0)
{
v___y_481_ = v___y_492_;
v___y_482_ = v___y_493_;
v___y_483_ = v_centenialCycles_495_;
v___y_484_ = v_remDays_497_;
v_quadrennialCycles_485_ = v_quadrennialCycles_498_;
goto v___jp_480_;
}
else
{
lean_object* v_quadrennialCycles_501_; 
v_quadrennialCycles_501_ = lean_int_sub(v_quadrennialCycles_498_, v___x_423_);
lean_dec(v_quadrennialCycles_498_);
v___y_481_ = v___y_492_;
v___y_482_ = v___y_493_;
v___y_483_ = v_centenialCycles_495_;
v___y_484_ = v_remDays_497_;
v_quadrennialCycles_485_ = v_quadrennialCycles_501_;
goto v___jp_480_;
}
}
v___jp_502_:
{
lean_object* v_centenialCycles_506_; uint8_t v___x_507_; 
v_centenialCycles_506_ = lean_int_ediv(v_remDays_505_, v_daysPer100Y_403_);
v___x_507_ = lean_int_dec_eq(v_centenialCycles_506_, v___x_404_);
if (v___x_507_ == 0)
{
v___y_492_ = v_quadracentennialCycles_504_;
v___y_493_ = v___y_503_;
v___y_494_ = v_remDays_505_;
v_centenialCycles_495_ = v_centenialCycles_506_;
goto v___jp_491_;
}
else
{
lean_object* v_centenialCycles_508_; 
v_centenialCycles_508_ = lean_int_sub(v_centenialCycles_506_, v___x_423_);
lean_dec(v_centenialCycles_506_);
v___y_492_ = v_quadracentennialCycles_504_;
v___y_493_ = v___y_503_;
v___y_494_ = v_remDays_505_;
v_centenialCycles_495_ = v_centenialCycles_508_;
goto v___jp_491_;
}
}
v___jp_509_:
{
lean_object* v_quadracentennialCycles_512_; lean_object* v_remDays_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_quadracentennialCycles_512_ = lean_int_ediv(v_snd_511_, v_daysPer400Y_401_);
v_remDays_513_ = lean_int_emod(v_snd_511_, v_daysPer400Y_401_);
lean_dec(v_snd_511_);
v___x_514_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_515_ = lean_int_dec_lt(v_remDays_513_, v___x_514_);
if (v___x_515_ == 0)
{
v___y_503_ = v_fst_510_;
v_quadracentennialCycles_504_ = v_quadracentennialCycles_512_;
v_remDays_505_ = v_remDays_513_;
goto v___jp_502_;
}
else
{
lean_object* v_remDays_516_; lean_object* v_quadracentennialCycles_517_; 
v_remDays_516_ = lean_int_add(v_remDays_513_, v_daysPer400Y_401_);
lean_dec(v_remDays_513_);
v_quadracentennialCycles_517_ = lean_int_sub(v_quadracentennialCycles_512_, v___x_423_);
lean_dec(v_quadracentennialCycles_512_);
v___y_503_ = v_fst_510_;
v_quadracentennialCycles_504_ = v_quadracentennialCycles_517_;
v_remDays_505_ = v_remDays_516_;
goto v___jp_502_;
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v_boundedDaysSinceEpoch_521_; lean_object* v_rawDays_522_; lean_object* v_h_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_520_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v_boundedDaysSinceEpoch_521_ = lean_int_div(v_snd_519_, v___x_520_);
v_rawDays_522_ = lean_int_sub(v_boundedDaysSinceEpoch_521_, v_leapYearEpoch_398_);
lean_dec(v_boundedDaysSinceEpoch_521_);
v_h_523_ = lean_int_mod(v_snd_519_, v___x_520_);
lean_dec(v_snd_519_);
v___x_524_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__31, &l_Std_Time_PlainDateTime_ofWallTime___closed__31_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31);
v___x_525_ = lean_int_dec_le(v_h_523_, v___x_524_);
if (v___x_525_ == 0)
{
v_fst_510_ = v_h_523_;
v_snd_511_ = v_rawDays_522_;
goto v___jp_509_;
}
else
{
lean_object* v___x_526_; lean_object* v_rawDays_527_; 
v___x_526_ = lean_int_add(v_h_523_, v___x_520_);
lean_dec(v_h_523_);
v_rawDays_527_ = lean_int_sub(v_rawDays_522_, v___x_423_);
lean_dec(v_rawDays_522_);
v_fst_510_ = v___x_526_;
v_snd_511_ = v_rawDays_527_;
goto v___jp_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(lean_object* v_as_534_, lean_object* v_as_x27_535_, lean_object* v_b_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_535_, v_b_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(lean_object* v_as_539_, lean_object* v_as_x27_540_, lean_object* v_b_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(v_as_539_, v_as_x27_540_, v_b_541_, v_a_542_);
lean_dec(v_as_x27_540_);
lean_dec(v_as_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object* v_pdt_544_){
_start:
{
lean_object* v_date_545_; lean_object* v___x_546_; 
v_date_545_ = lean_ctor_get(v_pdt_544_, 0);
lean_inc_ref(v_date_545_);
lean_dec_ref(v_pdt_544_);
v___x_546_ = l_Std_Time_PlainDate_toEpochDay(v_date_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object* v_days_547_, lean_object* v_time_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = l_Std_Time_PlainDate_ofEpochDay(v_days_547_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_time_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object* v_days_551_, lean_object* v_time_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_551_, v_time_552_);
lean_dec(v_days_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_554_, uint8_t v_desiredWeekday_555_){
_start:
{
lean_object* v_date_556_; lean_object* v_time_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_date_556_ = lean_ctor_get(v_dt_554_, 0);
v_time_557_ = lean_ctor_get(v_dt_554_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_dt_554_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v_dt_554_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_time_557_);
lean_inc(v_date_556_);
lean_dec(v_dt_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = l_Std_Time_PlainDate_withWeekday(v_date_556_, v_desiredWeekday_555_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_time_557_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_566_, lean_object* v_desiredWeekday_567_){
_start:
{
uint8_t v_desiredWeekday_boxed_568_; lean_object* v_res_569_; 
v_desiredWeekday_boxed_568_ = lean_unbox(v_desiredWeekday_567_);
v_res_569_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_566_, v_desiredWeekday_boxed_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_570_, lean_object* v_days_571_){
_start:
{
lean_object* v_date_572_; lean_object* v_time_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_613_; 
v_date_572_ = lean_ctor_get(v_dt_570_, 0);
v_time_573_ = lean_ctor_get(v_dt_570_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_dt_570_);
if (v_isSharedCheck_613_ == 0)
{
v___x_575_ = v_dt_570_;
v_isShared_576_ = v_isSharedCheck_613_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_time_573_);
lean_inc(v_date_572_);
lean_dec(v_dt_570_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_613_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_year_577_; lean_object* v_month_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_611_; 
v_year_577_ = lean_ctor_get(v_date_572_, 0);
v_month_578_ = lean_ctor_get(v_date_572_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_date_572_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_date_572_, 2);
lean_dec(v_unused_612_);
v___x_580_ = v_date_572_;
v_isShared_581_ = v_isSharedCheck_611_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_month_578_);
lean_inc(v_year_577_);
lean_dec(v_date_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_611_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint8_t v___y_583_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; uint8_t v___y_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_598_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_599_ = lean_int_mod(v_year_577_, v___x_598_);
v___x_600_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_601_ = lean_int_dec_eq(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
v___x_604_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_605_ = lean_int_mod(v_year_577_, v___x_604_);
v___x_606_ = lean_int_dec_eq(v___x_605_, v___x_600_);
lean_dec(v___x_605_);
if (v___x_606_ == 0)
{
uint8_t v___x_607_; 
v___x_607_ = 1;
v___y_603_ = v___x_607_;
goto v___jp_602_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_609_ = lean_int_mod(v_year_577_, v___x_608_);
v___x_610_ = lean_int_dec_eq(v___x_609_, v___x_600_);
lean_dec(v___x_609_);
v___y_603_ = v___x_610_;
goto v___jp_602_;
}
v___jp_582_:
{
lean_object* v_max_584_; uint8_t v___x_585_; 
v_max_584_ = l_Std_Time_Month_Ordinal_days(v___y_583_, v_month_578_);
v___x_585_ = lean_int_dec_lt(v_max_584_, v_days_571_);
if (v___x_585_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v_max_584_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v_days_571_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_year_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_month_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_days_571_);
v___x_587_ = v_reuseFailAlloc_591_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_587_);
v___x_589_ = v___x_575_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_time_573_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec(v_days_571_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v_max_584_);
v___x_593_ = v___x_580_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_year_577_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_month_578_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_max_584_);
v___x_593_ = v_reuseFailAlloc_597_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_595_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_593_);
v___x_595_ = v___x_575_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_time_573_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
v___jp_602_:
{
if (v___x_601_ == 0)
{
v___y_583_ = v___x_601_;
goto v___jp_582_;
}
else
{
v___y_583_ = v___y_603_;
goto v___jp_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_614_, lean_object* v_days_615_){
_start:
{
lean_object* v_date_616_; lean_object* v_time_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_627_; 
v_date_616_ = lean_ctor_get(v_dt_614_, 0);
v_time_617_ = lean_ctor_get(v_dt_614_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_dt_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_619_ = v_dt_614_;
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_time_617_);
lean_inc(v_date_616_);
lean_dec(v_dt_614_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_year_621_; lean_object* v_month_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_year_621_ = lean_ctor_get(v_date_616_, 0);
lean_inc(v_year_621_);
v_month_622_ = lean_ctor_get(v_date_616_, 1);
lean_inc(v_month_622_);
lean_dec_ref(v_date_616_);
v___x_623_ = l_Std_Time_PlainDate_rollOver(v_year_621_, v_month_622_, v_days_615_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_time_617_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_628_, lean_object* v_days_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_628_, v_days_629_);
lean_dec(v_days_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_631_, lean_object* v_month_632_){
_start:
{
lean_object* v_date_633_; lean_object* v_time_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_674_; 
v_date_633_ = lean_ctor_get(v_dt_631_, 0);
v_time_634_ = lean_ctor_get(v_dt_631_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_dt_631_);
if (v_isSharedCheck_674_ == 0)
{
v___x_636_ = v_dt_631_;
v_isShared_637_ = v_isSharedCheck_674_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_time_634_);
lean_inc(v_date_633_);
lean_dec(v_dt_631_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_674_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_year_638_; lean_object* v_day_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_672_; 
v_year_638_ = lean_ctor_get(v_date_633_, 0);
v_day_639_ = lean_ctor_get(v_date_633_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_date_633_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_date_633_, 1);
lean_dec(v_unused_673_);
v___x_641_ = v_date_633_;
v_isShared_642_ = v_isSharedCheck_672_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_day_639_);
lean_inc(v_year_638_);
lean_dec(v_date_633_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_672_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
uint8_t v___y_644_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; uint8_t v___y_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_659_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_660_ = lean_int_mod(v_year_638_, v___x_659_);
v___x_661_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_662_ = lean_int_dec_eq(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
v___x_665_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_666_ = lean_int_mod(v_year_638_, v___x_665_);
v___x_667_ = lean_int_dec_eq(v___x_666_, v___x_661_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
v___x_668_ = 1;
v___y_664_ = v___x_668_;
goto v___jp_663_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_670_ = lean_int_mod(v_year_638_, v___x_669_);
v___x_671_ = lean_int_dec_eq(v___x_670_, v___x_661_);
lean_dec(v___x_670_);
v___y_664_ = v___x_671_;
goto v___jp_663_;
}
v___jp_643_:
{
lean_object* v_max_645_; uint8_t v___x_646_; 
v_max_645_ = l_Std_Time_Month_Ordinal_days(v___y_644_, v_month_632_);
v___x_646_ = lean_int_dec_lt(v_max_645_, v_day_639_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
lean_dec(v_max_645_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_month_632_);
v___x_648_ = v___x_641_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_year_638_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_month_632_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_day_639_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_648_);
v___x_650_ = v___x_636_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_time_634_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_day_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 2, v_max_645_);
lean_ctor_set(v___x_641_, 1, v_month_632_);
v___x_654_ = v___x_641_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_year_638_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_month_632_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_max_645_);
v___x_654_ = v_reuseFailAlloc_658_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_654_);
v___x_656_ = v___x_636_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_time_634_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
v___jp_663_:
{
if (v___x_662_ == 0)
{
v___y_644_ = v___x_662_;
goto v___jp_643_;
}
else
{
v___y_644_ = v___y_664_;
goto v___jp_643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_675_, lean_object* v_month_676_){
_start:
{
lean_object* v_date_677_; lean_object* v_time_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
v_date_677_ = lean_ctor_get(v_dt_675_, 0);
v_time_678_ = lean_ctor_get(v_dt_675_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_dt_675_);
if (v_isSharedCheck_688_ == 0)
{
v___x_680_ = v_dt_675_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_time_678_);
lean_inc(v_date_677_);
lean_dec(v_dt_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_year_682_; lean_object* v_day_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v_year_682_ = lean_ctor_get(v_date_677_, 0);
lean_inc(v_year_682_);
v_day_683_ = lean_ctor_get(v_date_677_, 2);
lean_inc(v_day_683_);
lean_dec_ref(v_date_677_);
v___x_684_ = l_Std_Time_PlainDate_rollOver(v_year_682_, v_month_676_, v_day_683_);
lean_dec(v_day_683_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_684_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_time_678_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_689_, lean_object* v_year_690_){
_start:
{
lean_object* v_date_691_; lean_object* v_time_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_732_; 
v_date_691_ = lean_ctor_get(v_dt_689_, 0);
v_time_692_ = lean_ctor_get(v_dt_689_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_dt_689_);
if (v_isSharedCheck_732_ == 0)
{
v___x_694_ = v_dt_689_;
v_isShared_695_ = v_isSharedCheck_732_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_time_692_);
lean_inc(v_date_691_);
lean_dec(v_dt_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_732_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_month_696_; lean_object* v_day_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_730_; 
v_month_696_ = lean_ctor_get(v_date_691_, 1);
v_day_697_ = lean_ctor_get(v_date_691_, 2);
v_isSharedCheck_730_ = !lean_is_exclusive(v_date_691_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_date_691_, 0);
lean_dec(v_unused_731_);
v___x_699_ = v_date_691_;
v_isShared_700_ = v_isSharedCheck_730_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_day_697_);
lean_inc(v_month_696_);
lean_dec(v_date_691_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_730_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint8_t v___y_702_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; uint8_t v___y_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_717_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_718_ = lean_int_mod(v_year_690_, v___x_717_);
v___x_719_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_720_ = lean_int_dec_eq(v___x_718_, v___x_719_);
lean_dec(v___x_718_);
v___x_723_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_724_ = lean_int_mod(v_year_690_, v___x_723_);
v___x_725_ = lean_int_dec_eq(v___x_724_, v___x_719_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
uint8_t v___x_726_; 
v___x_726_ = 1;
v___y_722_ = v___x_726_;
goto v___jp_721_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_728_ = lean_int_mod(v_year_690_, v___x_727_);
v___x_729_ = lean_int_dec_eq(v___x_728_, v___x_719_);
lean_dec(v___x_728_);
v___y_722_ = v___x_729_;
goto v___jp_721_;
}
v___jp_701_:
{
lean_object* v_max_703_; uint8_t v___x_704_; 
v_max_703_ = l_Std_Time_Month_Ordinal_days(v___y_702_, v_month_696_);
v___x_704_ = lean_int_dec_lt(v_max_703_, v_day_697_);
if (v___x_704_ == 0)
{
lean_object* v___x_706_; 
lean_dec(v_max_703_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v_year_690_);
v___x_706_ = v___x_699_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_year_690_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_month_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_day_697_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_706_);
v___x_708_ = v___x_694_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_time_692_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v___x_712_; 
lean_dec(v_day_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 2, v_max_703_);
lean_ctor_set(v___x_699_, 0, v_year_690_);
v___x_712_ = v___x_699_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_year_690_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_month_696_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_max_703_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_712_);
v___x_714_ = v___x_694_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_time_692_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
v___jp_721_:
{
if (v___x_720_ == 0)
{
v___y_702_ = v___x_720_;
goto v___jp_701_;
}
else
{
v___y_702_ = v___y_722_;
goto v___jp_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_733_, lean_object* v_year_734_){
_start:
{
lean_object* v_date_735_; lean_object* v_time_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_746_; 
v_date_735_ = lean_ctor_get(v_dt_733_, 0);
v_time_736_ = lean_ctor_get(v_dt_733_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_dt_733_);
if (v_isSharedCheck_746_ == 0)
{
v___x_738_ = v_dt_733_;
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_time_736_);
lean_inc(v_date_735_);
lean_dec(v_dt_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_month_740_; lean_object* v_day_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v_month_740_ = lean_ctor_get(v_date_735_, 1);
lean_inc(v_month_740_);
v_day_741_ = lean_ctor_get(v_date_735_, 2);
lean_inc(v_day_741_);
lean_dec_ref(v_date_735_);
v___x_742_ = l_Std_Time_PlainDate_rollOver(v_year_734_, v_month_740_, v_day_741_);
lean_dec(v_day_741_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_time_736_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_747_, lean_object* v_hour_748_){
_start:
{
lean_object* v_time_749_; lean_object* v_date_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_768_; 
v_time_749_ = lean_ctor_get(v_dt_747_, 1);
v_date_750_ = lean_ctor_get(v_dt_747_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v_dt_747_);
if (v_isSharedCheck_768_ == 0)
{
v___x_752_ = v_dt_747_;
v_isShared_753_ = v_isSharedCheck_768_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_time_749_);
lean_inc(v_date_750_);
lean_dec(v_dt_747_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_768_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_minute_754_; lean_object* v_second_755_; lean_object* v_nanosecond_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_766_; 
v_minute_754_ = lean_ctor_get(v_time_749_, 1);
v_second_755_ = lean_ctor_get(v_time_749_, 2);
v_nanosecond_756_ = lean_ctor_get(v_time_749_, 3);
v_isSharedCheck_766_ = !lean_is_exclusive(v_time_749_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_time_749_, 0);
lean_dec(v_unused_767_);
v___x_758_ = v_time_749_;
v_isShared_759_ = v_isSharedCheck_766_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_nanosecond_756_);
lean_inc(v_second_755_);
lean_inc(v_minute_754_);
lean_dec(v_time_749_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_766_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_hour_748_);
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_hour_748_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_minute_754_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_second_755_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v_nanosecond_756_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_761_);
v___x_763_ = v___x_752_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_date_750_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_769_, lean_object* v_minute_770_){
_start:
{
lean_object* v_time_771_; lean_object* v_date_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_790_; 
v_time_771_ = lean_ctor_get(v_dt_769_, 1);
v_date_772_ = lean_ctor_get(v_dt_769_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_dt_769_);
if (v_isSharedCheck_790_ == 0)
{
v___x_774_ = v_dt_769_;
v_isShared_775_ = v_isSharedCheck_790_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_time_771_);
lean_inc(v_date_772_);
lean_dec(v_dt_769_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_790_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_hour_776_; lean_object* v_second_777_; lean_object* v_nanosecond_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_788_; 
v_hour_776_ = lean_ctor_get(v_time_771_, 0);
v_second_777_ = lean_ctor_get(v_time_771_, 2);
v_nanosecond_778_ = lean_ctor_get(v_time_771_, 3);
v_isSharedCheck_788_ = !lean_is_exclusive(v_time_771_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_time_771_, 1);
lean_dec(v_unused_789_);
v___x_780_ = v_time_771_;
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_nanosecond_778_);
lean_inc(v_second_777_);
lean_inc(v_hour_776_);
lean_dec(v_time_771_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v_minute_770_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_hour_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_minute_770_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_second_777_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_nanosecond_778_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_783_);
v___x_785_ = v___x_774_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_date_772_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_791_, lean_object* v_second_792_){
_start:
{
lean_object* v_time_793_; lean_object* v_date_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_812_; 
v_time_793_ = lean_ctor_get(v_dt_791_, 1);
v_date_794_ = lean_ctor_get(v_dt_791_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_dt_791_);
if (v_isSharedCheck_812_ == 0)
{
v___x_796_ = v_dt_791_;
v_isShared_797_ = v_isSharedCheck_812_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_time_793_);
lean_inc(v_date_794_);
lean_dec(v_dt_791_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_812_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_hour_798_; lean_object* v_minute_799_; lean_object* v_nanosecond_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_hour_798_ = lean_ctor_get(v_time_793_, 0);
v_minute_799_ = lean_ctor_get(v_time_793_, 1);
v_nanosecond_800_ = lean_ctor_get(v_time_793_, 3);
v_isSharedCheck_810_ = !lean_is_exclusive(v_time_793_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_time_793_, 2);
lean_dec(v_unused_811_);
v___x_802_ = v_time_793_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_nanosecond_800_);
lean_inc(v_minute_799_);
lean_inc(v_hour_798_);
lean_dec(v_time_793_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 2, v_second_792_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_hour_798_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_minute_799_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_second_792_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_nanosecond_800_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_805_);
v___x_807_ = v___x_796_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_date_794_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(1000u);
v___x_814_ = lean_nat_to_int(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1000000u);
v___x_816_ = lean_nat_to_int(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_817_, lean_object* v_millis_818_){
_start:
{
lean_object* v_time_819_; lean_object* v_date_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_843_; 
v_time_819_ = lean_ctor_get(v_dt_817_, 1);
v_date_820_ = lean_ctor_get(v_dt_817_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_dt_817_);
if (v_isSharedCheck_843_ == 0)
{
v___x_822_ = v_dt_817_;
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_time_819_);
lean_inc(v_date_820_);
lean_dec(v_dt_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_hour_824_; lean_object* v_minute_825_; lean_object* v_second_826_; lean_object* v_nanosecond_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_842_; 
v_hour_824_ = lean_ctor_get(v_time_819_, 0);
v_minute_825_ = lean_ctor_get(v_time_819_, 1);
v_second_826_ = lean_ctor_get(v_time_819_, 2);
v_nanosecond_827_ = lean_ctor_get(v_time_819_, 3);
v_isSharedCheck_842_ = !lean_is_exclusive(v_time_819_);
if (v_isSharedCheck_842_ == 0)
{
v___x_829_ = v_time_819_;
v_isShared_830_ = v_isSharedCheck_842_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_nanosecond_827_);
lean_inc(v_second_826_);
lean_inc(v_minute_825_);
lean_inc(v_hour_824_);
lean_dec(v_time_819_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_842_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_831_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_832_ = lean_int_emod(v_nanosecond_827_, v___x_831_);
lean_dec(v_nanosecond_827_);
v___x_833_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_834_ = lean_int_mul(v_millis_818_, v___x_833_);
v___x_835_ = lean_int_add(v___x_834_, v___x_832_);
lean_dec(v___x_832_);
lean_dec(v___x_834_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 3, v___x_835_);
v___x_837_ = v___x_829_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_hour_824_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_minute_825_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_second_826_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v___x_835_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_837_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_date_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_844_, lean_object* v_millis_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_844_, v_millis_845_);
lean_dec(v_millis_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_847_, lean_object* v_nano_848_){
_start:
{
lean_object* v_time_849_; lean_object* v_date_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_868_; 
v_time_849_ = lean_ctor_get(v_dt_847_, 1);
v_date_850_ = lean_ctor_get(v_dt_847_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v_dt_847_);
if (v_isSharedCheck_868_ == 0)
{
v___x_852_ = v_dt_847_;
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_time_849_);
lean_inc(v_date_850_);
lean_dec(v_dt_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_hour_854_; lean_object* v_minute_855_; lean_object* v_second_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_hour_854_ = lean_ctor_get(v_time_849_, 0);
v_minute_855_ = lean_ctor_get(v_time_849_, 1);
v_second_856_ = lean_ctor_get(v_time_849_, 2);
v_isSharedCheck_866_ = !lean_is_exclusive(v_time_849_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_time_849_, 3);
lean_dec(v_unused_867_);
v___x_858_ = v_time_849_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_second_856_);
lean_inc(v_minute_855_);
lean_inc(v_hour_854_);
lean_dec(v_time_849_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 3, v_nano_848_);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_hour_854_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_minute_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_second_856_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_nano_848_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_861_);
v___x_863_ = v___x_852_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_date_850_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_869_, lean_object* v_days_870_){
_start:
{
lean_object* v_date_871_; lean_object* v_time_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_882_; 
v_date_871_ = lean_ctor_get(v_dt_869_, 0);
v_time_872_ = lean_ctor_get(v_dt_869_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_dt_869_);
if (v_isSharedCheck_882_ == 0)
{
v___x_874_ = v_dt_869_;
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_time_872_);
lean_inc(v_date_871_);
lean_dec(v_dt_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_dateDays_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v_dateDays_876_ = l_Std_Time_PlainDate_toEpochDay(v_date_871_);
v___x_877_ = lean_int_add(v_dateDays_876_, v_days_870_);
lean_dec(v_dateDays_876_);
v___x_878_ = l_Std_Time_PlainDate_ofEpochDay(v___x_877_);
lean_dec(v___x_877_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_878_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_time_872_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_883_, lean_object* v_days_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_Time_PlainDateTime_addDays(v_dt_883_, v_days_884_);
lean_dec(v_days_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_886_, lean_object* v_days_887_){
_start:
{
lean_object* v_date_888_; lean_object* v_time_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_900_; 
v_date_888_ = lean_ctor_get(v_dt_886_, 0);
v_time_889_ = lean_ctor_get(v_dt_886_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_dt_886_);
if (v_isSharedCheck_900_ == 0)
{
v___x_891_ = v_dt_886_;
v_isShared_892_ = v_isSharedCheck_900_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_time_889_);
lean_inc(v_date_888_);
lean_dec(v_dt_886_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_900_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v_dateDays_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_893_ = lean_int_neg(v_days_887_);
v_dateDays_894_ = l_Std_Time_PlainDate_toEpochDay(v_date_888_);
v___x_895_ = lean_int_add(v_dateDays_894_, v___x_893_);
lean_dec(v___x_893_);
lean_dec(v_dateDays_894_);
v___x_896_ = l_Std_Time_PlainDate_ofEpochDay(v___x_895_);
lean_dec(v___x_895_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_896_);
v___x_898_ = v___x_891_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_time_889_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_901_, lean_object* v_days_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_Time_PlainDateTime_subDays(v_dt_901_, v_days_902_);
lean_dec(v_days_902_);
return v_res_903_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(7u);
v___x_905_ = lean_nat_to_int(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_906_, lean_object* v_weeks_907_){
_start:
{
lean_object* v_date_908_; lean_object* v_time_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_date_908_ = lean_ctor_get(v_dt_906_, 0);
v_time_909_ = lean_ctor_get(v_dt_906_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_dt_906_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v_dt_906_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_time_909_);
lean_inc(v_date_908_);
lean_dec(v_dt_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_dateDays_913_; lean_object* v___x_914_; lean_object* v_daysToAdd_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v_dateDays_913_ = l_Std_Time_PlainDate_toEpochDay(v_date_908_);
v___x_914_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_915_ = lean_int_mul(v_weeks_907_, v___x_914_);
v___x_916_ = lean_int_add(v_dateDays_913_, v_daysToAdd_915_);
lean_dec(v_daysToAdd_915_);
lean_dec(v_dateDays_913_);
v___x_917_ = l_Std_Time_PlainDate_ofEpochDay(v___x_916_);
lean_dec(v___x_916_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_917_);
v___x_919_ = v___x_911_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_time_909_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_922_, lean_object* v_weeks_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_922_, v_weeks_923_);
lean_dec(v_weeks_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_925_, lean_object* v_weeks_926_){
_start:
{
lean_object* v_date_927_; lean_object* v_time_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_941_; 
v_date_927_ = lean_ctor_get(v_dt_925_, 0);
v_time_928_ = lean_ctor_get(v_dt_925_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_dt_925_);
if (v_isSharedCheck_941_ == 0)
{
v___x_930_ = v_dt_925_;
v_isShared_931_ = v_isSharedCheck_941_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_time_928_);
lean_inc(v_date_927_);
lean_dec(v_dt_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_941_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v_dateDays_933_; lean_object* v___x_934_; lean_object* v_daysToAdd_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_932_ = lean_int_neg(v_weeks_926_);
v_dateDays_933_ = l_Std_Time_PlainDate_toEpochDay(v_date_927_);
v___x_934_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_935_ = lean_int_mul(v___x_932_, v___x_934_);
lean_dec(v___x_932_);
v___x_936_ = lean_int_add(v_dateDays_933_, v_daysToAdd_935_);
lean_dec(v_daysToAdd_935_);
lean_dec(v_dateDays_933_);
v___x_937_ = l_Std_Time_PlainDate_ofEpochDay(v___x_936_);
lean_dec(v___x_936_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_937_);
v___x_939_ = v___x_930_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_time_928_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_942_, lean_object* v_weeks_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_942_, v_weeks_943_);
lean_dec(v_weeks_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_945_, lean_object* v_months_946_){
_start:
{
lean_object* v_date_947_; lean_object* v_time_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_date_947_ = lean_ctor_get(v_dt_945_, 0);
v_time_948_ = lean_ctor_get(v_dt_945_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_dt_945_);
if (v_isSharedCheck_956_ == 0)
{
v___x_950_ = v_dt_945_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_time_948_);
lean_inc(v_date_947_);
lean_dec(v_dt_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = l_Std_Time_PlainDate_addMonthsClip(v_date_947_, v_months_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_time_948_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_957_, lean_object* v_months_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_957_, v_months_958_);
lean_dec(v_months_958_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_960_, lean_object* v_months_961_){
_start:
{
lean_object* v_date_962_; lean_object* v_time_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v_date_962_ = lean_ctor_get(v_dt_960_, 0);
v_time_963_ = lean_ctor_get(v_dt_960_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_dt_960_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v_dt_960_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_time_963_);
lean_inc(v_date_962_);
lean_dec(v_dt_960_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = lean_int_neg(v_months_961_);
v___x_968_ = l_Std_Time_PlainDate_addMonthsClip(v_date_962_, v___x_967_);
lean_dec(v___x_967_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_time_963_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_973_, lean_object* v_months_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_973_, v_months_974_);
lean_dec(v_months_974_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_976_, lean_object* v_months_977_){
_start:
{
lean_object* v_date_978_; lean_object* v_time_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_date_978_ = lean_ctor_get(v_dt_976_, 0);
v_time_979_ = lean_ctor_get(v_dt_976_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_dt_976_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v_dt_976_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_time_979_);
lean_inc(v_date_978_);
lean_dec(v_dt_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_978_, v_months_977_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_time_979_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_988_, lean_object* v_months_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_988_, v_months_989_);
lean_dec(v_months_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_991_, lean_object* v_months_992_){
_start:
{
lean_object* v_date_993_; lean_object* v_time_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
v_date_993_ = lean_ctor_get(v_dt_991_, 0);
v_time_994_ = lean_ctor_get(v_dt_991_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_dt_991_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_996_ = v_dt_991_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_time_994_);
lean_inc(v_date_993_);
lean_dec(v_dt_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_998_ = lean_int_neg(v_months_992_);
v___x_999_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_993_, v___x_998_);
lean_dec(v___x_998_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_time_994_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_1004_, lean_object* v_months_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_1004_, v_months_1005_);
lean_dec(v_months_1005_);
return v_res_1006_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_unsigned_to_nat(12u);
v___x_1008_ = lean_nat_to_int(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_1009_, lean_object* v_years_1010_){
_start:
{
lean_object* v_date_1011_; lean_object* v_time_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1022_; 
v_date_1011_ = lean_ctor_get(v_dt_1009_, 0);
v_time_1012_ = lean_ctor_get(v_dt_1009_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_dt_1009_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1014_ = v_dt_1009_;
v_isShared_1015_ = v_isSharedCheck_1022_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_time_1012_);
lean_inc(v_date_1011_);
lean_dec(v_dt_1009_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1022_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1016_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1017_ = lean_int_mul(v_years_1010_, v___x_1016_);
v___x_1018_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1011_, v___x_1017_);
lean_dec(v___x_1017_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1018_);
v___x_1020_ = v___x_1014_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_time_1012_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_1023_, lean_object* v_years_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_1023_, v_years_1024_);
lean_dec(v_years_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_1026_, lean_object* v_years_1027_){
_start:
{
lean_object* v_date_1028_; lean_object* v_time_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1039_; 
v_date_1028_ = lean_ctor_get(v_dt_1026_, 0);
v_time_1029_ = lean_ctor_get(v_dt_1026_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_dt_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1031_ = v_dt_1026_;
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_time_1029_);
lean_inc(v_date_1028_);
lean_dec(v_dt_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1033_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1034_ = lean_int_mul(v_years_1027_, v___x_1033_);
v___x_1035_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1028_, v___x_1034_);
lean_dec(v___x_1034_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_time_1029_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_1040_, lean_object* v_years_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_1040_, v_years_1041_);
lean_dec(v_years_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_1043_, lean_object* v_years_1044_){
_start:
{
lean_object* v_date_1045_; lean_object* v_time_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
v_date_1045_ = lean_ctor_get(v_dt_1043_, 0);
v_time_1046_ = lean_ctor_get(v_dt_1043_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_dt_1043_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1048_ = v_dt_1043_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_time_1046_);
lean_inc(v_date_1045_);
lean_dec(v_dt_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1050_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1051_ = lean_int_mul(v_years_1044_, v___x_1050_);
v___x_1052_ = lean_int_neg(v___x_1051_);
lean_dec(v___x_1051_);
v___x_1053_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1045_, v___x_1052_);
lean_dec(v___x_1052_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1053_);
v___x_1055_ = v___x_1048_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_time_1046_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_1058_, lean_object* v_years_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_1058_, v_years_1059_);
lean_dec(v_years_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_1061_, lean_object* v_years_1062_){
_start:
{
lean_object* v_date_1063_; lean_object* v_time_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
v_date_1063_ = lean_ctor_get(v_dt_1061_, 0);
v_time_1064_ = lean_ctor_get(v_dt_1061_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_dt_1061_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v_dt_1061_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_time_1064_);
lean_inc(v_date_1063_);
lean_dec(v_dt_1061_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1068_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1069_ = lean_int_mul(v_years_1062_, v___x_1068_);
v___x_1070_ = lean_int_neg(v___x_1069_);
lean_dec(v___x_1069_);
v___x_1071_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1063_, v___x_1070_);
lean_dec(v___x_1070_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1071_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_time_1064_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_1076_, lean_object* v_years_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_1076_, v_years_1077_);
lean_dec(v_years_1077_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_1079_, lean_object* v_nanos_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v_second_1082_; lean_object* v_nano_1083_; lean_object* v___x_1084_; lean_object* v_second_1085_; lean_object* v_nano_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_nanos_1089_; lean_object* v___x_1090_; lean_object* v_nanos_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1081_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1079_);
v_second_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_second_1082_);
v_nano_1083_ = lean_ctor_get(v___x_1081_, 1);
lean_inc(v_nano_1083_);
lean_dec_ref(v___x_1081_);
v___x_1084_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1080_);
v_second_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_second_1085_);
v_nano_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_nano_1086_);
lean_dec_ref(v___x_1084_);
v___x_1087_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1088_ = lean_int_mul(v_second_1082_, v___x_1087_);
lean_dec(v_second_1082_);
v_nanos_1089_ = lean_int_add(v___x_1088_, v_nano_1083_);
lean_dec(v_nano_1083_);
lean_dec(v___x_1088_);
v___x_1090_ = lean_int_mul(v_second_1085_, v___x_1087_);
lean_dec(v_second_1085_);
v_nanos_1091_ = lean_int_add(v___x_1090_, v_nano_1086_);
lean_dec(v_nano_1086_);
lean_dec(v___x_1090_);
v___x_1092_ = lean_int_add(v_nanos_1089_, v_nanos_1091_);
lean_dec(v_nanos_1091_);
lean_dec(v_nanos_1089_);
v___x_1093_ = l_Std_Time_Duration_ofNanoseconds(v___x_1092_);
lean_dec(v___x_1092_);
v___x_1094_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_1095_, lean_object* v_nanos_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_1095_, v_nanos_1096_);
lean_dec(v_nanos_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_1098_, lean_object* v_nanos_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v_second_1101_; lean_object* v_nano_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_second_1105_; lean_object* v_nano_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_nanos_1109_; lean_object* v___x_1110_; lean_object* v_nanos_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1100_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1098_);
v_second_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_second_1101_);
v_nano_1102_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_nano_1102_);
lean_dec_ref(v___x_1100_);
v___x_1103_ = lean_int_neg(v_nanos_1099_);
v___x_1104_ = l_Std_Time_Duration_ofNanoseconds(v___x_1103_);
lean_dec(v___x_1103_);
v_second_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_second_1105_);
v_nano_1106_ = lean_ctor_get(v___x_1104_, 1);
lean_inc(v_nano_1106_);
lean_dec_ref(v___x_1104_);
v___x_1107_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1108_ = lean_int_mul(v_second_1101_, v___x_1107_);
lean_dec(v_second_1101_);
v_nanos_1109_ = lean_int_add(v___x_1108_, v_nano_1102_);
lean_dec(v_nano_1102_);
lean_dec(v___x_1108_);
v___x_1110_ = lean_int_mul(v_second_1105_, v___x_1107_);
lean_dec(v_second_1105_);
v_nanos_1111_ = lean_int_add(v___x_1110_, v_nano_1106_);
lean_dec(v_nano_1106_);
lean_dec(v___x_1110_);
v___x_1112_ = lean_int_add(v_nanos_1109_, v_nanos_1111_);
lean_dec(v_nanos_1111_);
lean_dec(v_nanos_1109_);
v___x_1113_ = l_Std_Time_Duration_ofNanoseconds(v___x_1112_);
lean_dec(v___x_1112_);
v___x_1114_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_1115_, lean_object* v_nanos_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_1115_, v_nanos_1116_);
lean_dec(v_nanos_1116_);
return v_res_1117_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_cstr_to_nat("3600000000000");
v___x_1119_ = lean_nat_to_int(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_1120_, lean_object* v_hours_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v_second_1123_; lean_object* v_nano_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_second_1128_; lean_object* v_nano_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_nanos_1132_; lean_object* v___x_1133_; lean_object* v_nanos_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1122_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1120_);
v_second_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_second_1123_);
v_nano_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_nano_1124_);
lean_dec_ref(v___x_1122_);
v___x_1125_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1126_ = lean_int_mul(v_hours_1121_, v___x_1125_);
v___x_1127_ = l_Std_Time_Duration_ofNanoseconds(v___x_1126_);
lean_dec(v___x_1126_);
v_second_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_second_1128_);
v_nano_1129_ = lean_ctor_get(v___x_1127_, 1);
lean_inc(v_nano_1129_);
lean_dec_ref(v___x_1127_);
v___x_1130_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1131_ = lean_int_mul(v_second_1123_, v___x_1130_);
lean_dec(v_second_1123_);
v_nanos_1132_ = lean_int_add(v___x_1131_, v_nano_1124_);
lean_dec(v_nano_1124_);
lean_dec(v___x_1131_);
v___x_1133_ = lean_int_mul(v_second_1128_, v___x_1130_);
lean_dec(v_second_1128_);
v_nanos_1134_ = lean_int_add(v___x_1133_, v_nano_1129_);
lean_dec(v_nano_1129_);
lean_dec(v___x_1133_);
v___x_1135_ = lean_int_add(v_nanos_1132_, v_nanos_1134_);
lean_dec(v_nanos_1134_);
lean_dec(v_nanos_1132_);
v___x_1136_ = l_Std_Time_Duration_ofNanoseconds(v___x_1135_);
lean_dec(v___x_1135_);
v___x_1137_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_1138_, lean_object* v_hours_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Std_Time_PlainDateTime_addHours(v_dt_1138_, v_hours_1139_);
lean_dec(v_hours_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_1141_, lean_object* v_hours_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v_second_1144_; lean_object* v_nano_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_second_1150_; lean_object* v_nano_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_nanos_1154_; lean_object* v___x_1155_; lean_object* v_nanos_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1143_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1141_);
v_second_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_second_1144_);
v_nano_1145_ = lean_ctor_get(v___x_1143_, 1);
lean_inc(v_nano_1145_);
lean_dec_ref(v___x_1143_);
v___x_1146_ = lean_int_neg(v_hours_1142_);
v___x_1147_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1148_ = lean_int_mul(v___x_1146_, v___x_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = l_Std_Time_Duration_ofNanoseconds(v___x_1148_);
lean_dec(v___x_1148_);
v_second_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_second_1150_);
v_nano_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_nano_1151_);
lean_dec_ref(v___x_1149_);
v___x_1152_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1153_ = lean_int_mul(v_second_1144_, v___x_1152_);
lean_dec(v_second_1144_);
v_nanos_1154_ = lean_int_add(v___x_1153_, v_nano_1145_);
lean_dec(v_nano_1145_);
lean_dec(v___x_1153_);
v___x_1155_ = lean_int_mul(v_second_1150_, v___x_1152_);
lean_dec(v_second_1150_);
v_nanos_1156_ = lean_int_add(v___x_1155_, v_nano_1151_);
lean_dec(v_nano_1151_);
lean_dec(v___x_1155_);
v___x_1157_ = lean_int_add(v_nanos_1154_, v_nanos_1156_);
lean_dec(v_nanos_1156_);
lean_dec(v_nanos_1154_);
v___x_1158_ = l_Std_Time_Duration_ofNanoseconds(v___x_1157_);
lean_dec(v___x_1157_);
v___x_1159_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_1160_, lean_object* v_hours_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_Time_PlainDateTime_subHours(v_dt_1160_, v_hours_1161_);
lean_dec(v_hours_1161_);
return v_res_1162_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_cstr_to_nat("60000000000");
v___x_1164_ = lean_nat_to_int(v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_1165_, lean_object* v_minutes_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v_second_1168_; lean_object* v_nano_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_second_1173_; lean_object* v_nano_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_nanos_1177_; lean_object* v___x_1178_; lean_object* v_nanos_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1167_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1165_);
v_second_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_second_1168_);
v_nano_1169_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_nano_1169_);
lean_dec_ref(v___x_1167_);
v___x_1170_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1171_ = lean_int_mul(v_minutes_1166_, v___x_1170_);
v___x_1172_ = l_Std_Time_Duration_ofNanoseconds(v___x_1171_);
lean_dec(v___x_1171_);
v_second_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_second_1173_);
v_nano_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc(v_nano_1174_);
lean_dec_ref(v___x_1172_);
v___x_1175_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1176_ = lean_int_mul(v_second_1168_, v___x_1175_);
lean_dec(v_second_1168_);
v_nanos_1177_ = lean_int_add(v___x_1176_, v_nano_1169_);
lean_dec(v_nano_1169_);
lean_dec(v___x_1176_);
v___x_1178_ = lean_int_mul(v_second_1173_, v___x_1175_);
lean_dec(v_second_1173_);
v_nanos_1179_ = lean_int_add(v___x_1178_, v_nano_1174_);
lean_dec(v_nano_1174_);
lean_dec(v___x_1178_);
v___x_1180_ = lean_int_add(v_nanos_1177_, v_nanos_1179_);
lean_dec(v_nanos_1179_);
lean_dec(v_nanos_1177_);
v___x_1181_ = l_Std_Time_Duration_ofNanoseconds(v___x_1180_);
lean_dec(v___x_1180_);
v___x_1182_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_1183_, lean_object* v_minutes_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_1183_, v_minutes_1184_);
lean_dec(v_minutes_1184_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_1186_, lean_object* v_minutes_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v_second_1189_; lean_object* v_nano_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_second_1195_; lean_object* v_nano_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_nanos_1199_; lean_object* v___x_1200_; lean_object* v_nanos_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1188_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1186_);
v_second_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_second_1189_);
v_nano_1190_ = lean_ctor_get(v___x_1188_, 1);
lean_inc(v_nano_1190_);
lean_dec_ref(v___x_1188_);
v___x_1191_ = lean_int_neg(v_minutes_1187_);
v___x_1192_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1193_ = lean_int_mul(v___x_1191_, v___x_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = l_Std_Time_Duration_ofNanoseconds(v___x_1193_);
lean_dec(v___x_1193_);
v_second_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_second_1195_);
v_nano_1196_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_nano_1196_);
lean_dec_ref(v___x_1194_);
v___x_1197_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1198_ = lean_int_mul(v_second_1189_, v___x_1197_);
lean_dec(v_second_1189_);
v_nanos_1199_ = lean_int_add(v___x_1198_, v_nano_1190_);
lean_dec(v_nano_1190_);
lean_dec(v___x_1198_);
v___x_1200_ = lean_int_mul(v_second_1195_, v___x_1197_);
lean_dec(v_second_1195_);
v_nanos_1201_ = lean_int_add(v___x_1200_, v_nano_1196_);
lean_dec(v_nano_1196_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_int_add(v_nanos_1199_, v_nanos_1201_);
lean_dec(v_nanos_1201_);
lean_dec(v_nanos_1199_);
v___x_1203_ = l_Std_Time_Duration_ofNanoseconds(v___x_1202_);
lean_dec(v___x_1202_);
v___x_1204_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_1205_, lean_object* v_minutes_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_1205_, v_minutes_1206_);
lean_dec(v_minutes_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_1208_, lean_object* v_seconds_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v_second_1211_; lean_object* v_nano_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_second_1216_; lean_object* v_nano_1217_; lean_object* v___x_1218_; lean_object* v_nanos_1219_; lean_object* v___x_1220_; lean_object* v_nanos_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1210_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1208_);
v_second_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_second_1211_);
v_nano_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_nano_1212_);
lean_dec_ref(v___x_1210_);
v___x_1213_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1214_ = lean_int_mul(v_seconds_1209_, v___x_1213_);
v___x_1215_ = l_Std_Time_Duration_ofNanoseconds(v___x_1214_);
lean_dec(v___x_1214_);
v_second_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_second_1216_);
v_nano_1217_ = lean_ctor_get(v___x_1215_, 1);
lean_inc(v_nano_1217_);
lean_dec_ref(v___x_1215_);
v___x_1218_ = lean_int_mul(v_second_1211_, v___x_1213_);
lean_dec(v_second_1211_);
v_nanos_1219_ = lean_int_add(v___x_1218_, v_nano_1212_);
lean_dec(v_nano_1212_);
lean_dec(v___x_1218_);
v___x_1220_ = lean_int_mul(v_second_1216_, v___x_1213_);
lean_dec(v_second_1216_);
v_nanos_1221_ = lean_int_add(v___x_1220_, v_nano_1217_);
lean_dec(v_nano_1217_);
lean_dec(v___x_1220_);
v___x_1222_ = lean_int_add(v_nanos_1219_, v_nanos_1221_);
lean_dec(v_nanos_1221_);
lean_dec(v_nanos_1219_);
v___x_1223_ = l_Std_Time_Duration_ofNanoseconds(v___x_1222_);
lean_dec(v___x_1222_);
v___x_1224_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_1225_, lean_object* v_seconds_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_1225_, v_seconds_1226_);
lean_dec(v_seconds_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_1228_, lean_object* v_seconds_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v_second_1231_; lean_object* v_nano_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_second_1237_; lean_object* v_nano_1238_; lean_object* v___x_1239_; lean_object* v_nanos_1240_; lean_object* v___x_1241_; lean_object* v_nanos_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1230_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1228_);
v_second_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_second_1231_);
v_nano_1232_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_nano_1232_);
lean_dec_ref(v___x_1230_);
v___x_1233_ = lean_int_neg(v_seconds_1229_);
v___x_1234_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1235_ = lean_int_mul(v___x_1233_, v___x_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = l_Std_Time_Duration_ofNanoseconds(v___x_1235_);
lean_dec(v___x_1235_);
v_second_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_second_1237_);
v_nano_1238_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_nano_1238_);
lean_dec_ref(v___x_1236_);
v___x_1239_ = lean_int_mul(v_second_1231_, v___x_1234_);
lean_dec(v_second_1231_);
v_nanos_1240_ = lean_int_add(v___x_1239_, v_nano_1232_);
lean_dec(v_nano_1232_);
lean_dec(v___x_1239_);
v___x_1241_ = lean_int_mul(v_second_1237_, v___x_1234_);
lean_dec(v_second_1237_);
v_nanos_1242_ = lean_int_add(v___x_1241_, v_nano_1238_);
lean_dec(v_nano_1238_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_int_add(v_nanos_1240_, v_nanos_1242_);
lean_dec(v_nanos_1242_);
lean_dec(v_nanos_1240_);
v___x_1244_ = l_Std_Time_Duration_ofNanoseconds(v___x_1243_);
lean_dec(v___x_1243_);
v___x_1245_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_1246_, lean_object* v_seconds_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_1246_, v_seconds_1247_);
lean_dec(v_seconds_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_1249_, lean_object* v_milliseconds_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v_second_1252_; lean_object* v_nano_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_second_1257_; lean_object* v_nano_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_nanos_1261_; lean_object* v___x_1262_; lean_object* v_nanos_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1251_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1249_);
v_second_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_second_1252_);
v_nano_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_nano_1253_);
lean_dec_ref(v___x_1251_);
v___x_1254_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1255_ = lean_int_mul(v_milliseconds_1250_, v___x_1254_);
v___x_1256_ = l_Std_Time_Duration_ofNanoseconds(v___x_1255_);
lean_dec(v___x_1255_);
v_second_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_second_1257_);
v_nano_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_nano_1258_);
lean_dec_ref(v___x_1256_);
v___x_1259_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1260_ = lean_int_mul(v_second_1252_, v___x_1259_);
lean_dec(v_second_1252_);
v_nanos_1261_ = lean_int_add(v___x_1260_, v_nano_1253_);
lean_dec(v_nano_1253_);
lean_dec(v___x_1260_);
v___x_1262_ = lean_int_mul(v_second_1257_, v___x_1259_);
lean_dec(v_second_1257_);
v_nanos_1263_ = lean_int_add(v___x_1262_, v_nano_1258_);
lean_dec(v_nano_1258_);
lean_dec(v___x_1262_);
v___x_1264_ = lean_int_add(v_nanos_1261_, v_nanos_1263_);
lean_dec(v_nanos_1263_);
lean_dec(v_nanos_1261_);
v___x_1265_ = l_Std_Time_Duration_ofNanoseconds(v___x_1264_);
lean_dec(v___x_1264_);
v___x_1266_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_1267_, lean_object* v_milliseconds_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_1267_, v_milliseconds_1268_);
lean_dec(v_milliseconds_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_1270_, lean_object* v_milliseconds_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v_second_1273_; lean_object* v_nano_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_second_1279_; lean_object* v_nano_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_nanos_1283_; lean_object* v___x_1284_; lean_object* v_nanos_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1272_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1270_);
v_second_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_second_1273_);
v_nano_1274_ = lean_ctor_get(v___x_1272_, 1);
lean_inc(v_nano_1274_);
lean_dec_ref(v___x_1272_);
v___x_1275_ = lean_int_neg(v_milliseconds_1271_);
v___x_1276_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1277_ = lean_int_mul(v___x_1275_, v___x_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = l_Std_Time_Duration_ofNanoseconds(v___x_1277_);
lean_dec(v___x_1277_);
v_second_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_second_1279_);
v_nano_1280_ = lean_ctor_get(v___x_1278_, 1);
lean_inc(v_nano_1280_);
lean_dec_ref(v___x_1278_);
v___x_1281_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1282_ = lean_int_mul(v_second_1273_, v___x_1281_);
lean_dec(v_second_1273_);
v_nanos_1283_ = lean_int_add(v___x_1282_, v_nano_1274_);
lean_dec(v_nano_1274_);
lean_dec(v___x_1282_);
v___x_1284_ = lean_int_mul(v_second_1279_, v___x_1281_);
lean_dec(v_second_1279_);
v_nanos_1285_ = lean_int_add(v___x_1284_, v_nano_1280_);
lean_dec(v_nano_1280_);
lean_dec(v___x_1284_);
v___x_1286_ = lean_int_add(v_nanos_1283_, v_nanos_1285_);
lean_dec(v_nanos_1285_);
lean_dec(v_nanos_1283_);
v___x_1287_ = l_Std_Time_Duration_ofNanoseconds(v___x_1286_);
lean_dec(v___x_1286_);
v___x_1288_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1289_, lean_object* v_milliseconds_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1289_, v_milliseconds_1290_);
lean_dec(v_milliseconds_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1292_){
_start:
{
lean_object* v_date_1293_; lean_object* v_year_1294_; 
v_date_1293_ = lean_ctor_get(v_dt_1292_, 0);
v_year_1294_ = lean_ctor_get(v_date_1293_, 0);
lean_inc(v_year_1294_);
return v_year_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_Time_PlainDateTime_year(v_dt_1295_);
lean_dec_ref(v_dt_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1297_){
_start:
{
lean_object* v_date_1298_; lean_object* v_month_1299_; 
v_date_1298_ = lean_ctor_get(v_dt_1297_, 0);
v_month_1299_ = lean_ctor_get(v_date_1298_, 1);
lean_inc(v_month_1299_);
return v_month_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_Time_PlainDateTime_month(v_dt_1300_);
lean_dec_ref(v_dt_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1302_){
_start:
{
lean_object* v_date_1303_; lean_object* v_day_1304_; 
v_date_1303_ = lean_ctor_get(v_dt_1302_, 0);
v_day_1304_ = lean_ctor_get(v_date_1303_, 2);
lean_inc(v_day_1304_);
return v_day_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Std_Time_PlainDateTime_day(v_dt_1305_);
lean_dec_ref(v_dt_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1307_){
_start:
{
lean_object* v_date_1308_; uint8_t v___x_1309_; 
v_date_1308_ = lean_ctor_get(v_dt_1307_, 0);
lean_inc_ref(v_date_1308_);
lean_dec_ref(v_dt_1307_);
v___x_1309_ = l_Std_Time_PlainDate_weekday(v_date_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Std_Time_PlainDateTime_weekday(v_dt_1310_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1313_){
_start:
{
lean_object* v_time_1314_; lean_object* v_hour_1315_; 
v_time_1314_ = lean_ctor_get(v_dt_1313_, 1);
v_hour_1315_ = lean_ctor_get(v_time_1314_, 0);
lean_inc(v_hour_1315_);
return v_hour_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Std_Time_PlainDateTime_hour(v_dt_1316_);
lean_dec_ref(v_dt_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1318_){
_start:
{
lean_object* v_time_1319_; lean_object* v_minute_1320_; 
v_time_1319_ = lean_ctor_get(v_dt_1318_, 1);
v_minute_1320_ = lean_ctor_get(v_time_1319_, 1);
lean_inc(v_minute_1320_);
return v_minute_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_Time_PlainDateTime_minute(v_dt_1321_);
lean_dec_ref(v_dt_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1323_){
_start:
{
lean_object* v_time_1324_; lean_object* v_nanosecond_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_time_1324_ = lean_ctor_get(v_dt_1323_, 1);
v_nanosecond_1325_ = lean_ctor_get(v_time_1324_, 3);
v___x_1326_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1327_ = lean_int_ediv(v_nanosecond_1325_, v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1328_);
lean_dec_ref(v_dt_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1330_){
_start:
{
lean_object* v_time_1331_; lean_object* v_second_1332_; 
v_time_1331_ = lean_ctor_get(v_dt_1330_, 1);
v_second_1332_ = lean_ctor_get(v_time_1331_, 2);
lean_inc(v_second_1332_);
return v_second_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_Time_PlainDateTime_second(v_dt_1333_);
lean_dec_ref(v_dt_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1335_){
_start:
{
lean_object* v_time_1336_; lean_object* v_nanosecond_1337_; 
v_time_1336_ = lean_ctor_get(v_dt_1335_, 1);
v_nanosecond_1337_ = lean_ctor_get(v_time_1336_, 3);
lean_inc(v_nanosecond_1337_);
return v_nanosecond_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1338_);
lean_dec_ref(v_dt_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1340_){
_start:
{
lean_object* v_date_1341_; lean_object* v_year_1342_; uint8_t v___x_1343_; 
v_date_1341_ = lean_ctor_get(v_date_1340_, 0);
v_year_1342_ = lean_ctor_get(v_date_1341_, 0);
v___x_1343_ = l_Std_Time_Year_Offset_era(v_year_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1344_){
_start:
{
uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_res_1345_ = l_Std_Time_PlainDateTime_era(v_date_1344_);
lean_dec_ref(v_date_1344_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1347_){
_start:
{
lean_object* v_date_1348_; lean_object* v_year_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_date_1348_ = lean_ctor_get(v_date_1347_, 0);
v_year_1349_ = lean_ctor_get(v_date_1348_, 0);
v___x_1350_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1351_ = lean_int_mod(v_year_1349_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1353_ = lean_int_dec_eq(v___x_1351_, v___x_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1355_ = lean_int_mod(v_year_1349_, v___x_1354_);
v___x_1356_ = lean_int_dec_eq(v___x_1355_, v___x_1352_);
lean_dec(v___x_1355_);
if (v___x_1356_ == 0)
{
return v___x_1353_;
}
else
{
if (v___x_1353_ == 0)
{
return v___x_1353_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1358_ = lean_int_mod(v_year_1349_, v___x_1357_);
v___x_1359_ = lean_int_dec_eq(v___x_1358_, v___x_1352_);
lean_dec(v___x_1358_);
return v___x_1359_;
}
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1363_, uint8_t v_firstDay_1364_, lean_object* v_minDays_1365_){
_start:
{
lean_object* v_date_1366_; lean_object* v___x_1367_; 
v_date_1366_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1366_);
lean_dec_ref(v_date_1363_);
v___x_1367_ = l_Std_Time_PlainDate_weekOfYear(v_date_1366_, v_firstDay_1364_, v_minDays_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear___boxed(lean_object* v_date_1368_, lean_object* v_firstDay_1369_, lean_object* v_minDays_1370_){
_start:
{
uint8_t v_firstDay_boxed_1371_; lean_object* v_res_1372_; 
v_firstDay_boxed_1371_ = lean_unbox(v_firstDay_1369_);
v_res_1372_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_1368_, v_firstDay_boxed_1371_, v_minDays_1370_);
lean_dec(v_minDays_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object* v_date_1373_, uint8_t v_firstDay_1374_, lean_object* v_minDays_1375_){
_start:
{
lean_object* v_date_1376_; lean_object* v___x_1377_; 
v_date_1376_ = lean_ctor_get(v_date_1373_, 0);
lean_inc_ref(v_date_1376_);
lean_dec_ref(v_date_1373_);
v___x_1377_ = l_Std_Time_PlainDate_weekYear(v_date_1376_, v_firstDay_1374_, v_minDays_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object* v_date_1378_, lean_object* v_firstDay_1379_, lean_object* v_minDays_1380_){
_start:
{
uint8_t v_firstDay_boxed_1381_; lean_object* v_res_1382_; 
v_firstDay_boxed_1381_ = lean_unbox(v_firstDay_1379_);
v_res_1382_ = l_Std_Time_PlainDateTime_weekYear(v_date_1378_, v_firstDay_boxed_1381_, v_minDays_1380_);
lean_dec(v_minDays_1380_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1383_){
_start:
{
lean_object* v_date_1384_; lean_object* v___x_1385_; 
v_date_1384_ = lean_ctor_get(v_date_1383_, 0);
v___x_1385_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1386_);
lean_dec_ref(v_date_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1388_, uint8_t v_firstDay_1389_){
_start:
{
lean_object* v_date_1390_; lean_object* v___x_1391_; 
v_date_1390_ = lean_ctor_get(v_date_1388_, 0);
lean_inc_ref(v_date_1390_);
lean_dec_ref(v_date_1388_);
v___x_1391_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1390_, v_firstDay_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1392_, lean_object* v_firstDay_1393_){
_start:
{
uint8_t v_firstDay_boxed_1394_; lean_object* v_res_1395_; 
v_firstDay_boxed_1394_ = lean_unbox(v_firstDay_1393_);
v_res_1395_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1392_, v_firstDay_boxed_1394_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1396_){
_start:
{
lean_object* v_date_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1423_; 
v_date_1397_ = lean_ctor_get(v_date_1396_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_date_1396_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_date_1396_, 1);
lean_dec(v_unused_1424_);
v___x_1399_ = v_date_1396_;
v_isShared_1400_ = v_isSharedCheck_1423_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_date_1397_);
lean_dec(v_date_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1423_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_year_1401_; lean_object* v_month_1402_; lean_object* v_day_1403_; uint8_t v___y_1405_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; uint8_t v___y_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_year_1401_ = lean_ctor_get(v_date_1397_, 0);
lean_inc(v_year_1401_);
v_month_1402_ = lean_ctor_get(v_date_1397_, 1);
lean_inc(v_month_1402_);
v_day_1403_ = lean_ctor_get(v_date_1397_, 2);
lean_inc(v_day_1403_);
lean_dec_ref(v_date_1397_);
v___x_1410_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1411_ = lean_int_mod(v_year_1401_, v___x_1410_);
v___x_1412_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1413_ = lean_int_dec_eq(v___x_1411_, v___x_1412_);
lean_dec(v___x_1411_);
v___x_1416_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1417_ = lean_int_mod(v_year_1401_, v___x_1416_);
v___x_1418_ = lean_int_dec_eq(v___x_1417_, v___x_1412_);
lean_dec(v___x_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
lean_dec(v_year_1401_);
v___x_1419_ = 1;
v___y_1415_ = v___x_1419_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1421_ = lean_int_mod(v_year_1401_, v___x_1420_);
lean_dec(v_year_1401_);
v___x_1422_ = lean_int_dec_eq(v___x_1421_, v___x_1412_);
lean_dec(v___x_1421_);
v___y_1415_ = v___x_1422_;
goto v___jp_1414_;
}
v___jp_1404_:
{
lean_object* v___x_1407_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v_day_1403_);
lean_ctor_set(v___x_1399_, 0, v_month_1402_);
v___x_1407_ = v___x_1399_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_month_1402_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_day_1403_);
v___x_1407_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Std_Time_ValidDate_dayOfYear(v___y_1405_, v___x_1407_);
lean_dec_ref(v___x_1407_);
return v___x_1408_;
}
}
v___jp_1414_:
{
if (v___x_1413_ == 0)
{
v___y_1405_ = v___x_1413_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v___y_1415_;
goto v___jp_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object* v_date_1425_){
_start:
{
lean_object* v_date_1426_; lean_object* v___x_1427_; 
v_date_1426_ = lean_ctor_get(v_date_1425_, 0);
v___x_1427_ = l_Std_Time_PlainDate_quarter(v_date_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object* v_date_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_Time_PlainDateTime_quarter(v_date_1428_);
lean_dec_ref(v_date_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object* v_date_1430_, lean_object* v_time_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_date_1430_);
lean_ctor_set(v___x_1432_, 1, v_time_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object* v_time_1433_, lean_object* v_date_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_date_1434_);
lean_ctor_set(v___x_1435_, 1, v_time_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object* v_x_1464_, lean_object* v_y_1465_){
_start:
{
lean_object* v_second_1466_; lean_object* v_nano_1467_; lean_object* v___x_1468_; lean_object* v_second_1469_; lean_object* v_nano_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v_nanos_1473_; lean_object* v___x_1474_; lean_object* v_second_1475_; lean_object* v_nano_1476_; lean_object* v___x_1477_; lean_object* v_nanos_1478_; lean_object* v___x_1479_; lean_object* v_nanos_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_second_1466_ = lean_ctor_get(v_y_1465_, 0);
v_nano_1467_ = lean_ctor_get(v_y_1465_, 1);
v___x_1468_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1464_);
v_second_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_second_1469_);
v_nano_1470_ = lean_ctor_get(v___x_1468_, 1);
lean_inc(v_nano_1470_);
lean_dec_ref(v___x_1468_);
v___x_1471_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1472_ = lean_int_mul(v_second_1466_, v___x_1471_);
v_nanos_1473_ = lean_int_add(v___x_1472_, v_nano_1467_);
lean_dec(v___x_1472_);
v___x_1474_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1473_);
lean_dec(v_nanos_1473_);
v_second_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_second_1475_);
v_nano_1476_ = lean_ctor_get(v___x_1474_, 1);
lean_inc(v_nano_1476_);
lean_dec_ref(v___x_1474_);
v___x_1477_ = lean_int_mul(v_second_1469_, v___x_1471_);
lean_dec(v_second_1469_);
v_nanos_1478_ = lean_int_add(v___x_1477_, v_nano_1470_);
lean_dec(v_nano_1470_);
lean_dec(v___x_1477_);
v___x_1479_ = lean_int_mul(v_second_1475_, v___x_1471_);
lean_dec(v_second_1475_);
v_nanos_1480_ = lean_int_add(v___x_1479_, v_nano_1476_);
lean_dec(v_nano_1476_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_int_add(v_nanos_1478_, v_nanos_1480_);
lean_dec(v_nanos_1480_);
lean_dec(v_nanos_1478_);
v___x_1482_ = l_Std_Time_Duration_ofNanoseconds(v___x_1481_);
lean_dec(v___x_1481_);
v___x_1483_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1484_, lean_object* v_y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_1484_, v_y_1485_);
lean_dec_ref(v_y_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_1489_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = l_Std_Time_PlainTime_midnight;
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_date_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_1492_){
_start:
{
lean_object* v_date_1493_; 
v_date_1493_ = lean_ctor_get(v_pdt_1492_, 0);
lean_inc_ref(v_date_1493_);
return v_date_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_1494_);
lean_dec_ref(v_pdt_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_1496_){
_start:
{
lean_object* v_time_1497_; 
v_time_1497_ = lean_ctor_get(v_pdt_1496_, 1);
lean_inc_ref(v_time_1497_);
return v_time_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_1498_);
lean_dec_ref(v_pdt_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_1500_, lean_object* v_y_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v_second_1503_; lean_object* v_nano_1504_; lean_object* v___x_1505_; lean_object* v_second_1506_; lean_object* v_nano_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_nanos_1512_; lean_object* v___x_1513_; lean_object* v_nanos_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1502_ = l_Std_Time_PlainDateTime_toWallTime(v_y_1501_);
v_second_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_second_1503_);
v_nano_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_nano_1504_);
lean_dec_ref(v___x_1502_);
v___x_1505_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1500_);
v_second_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_second_1506_);
v_nano_1507_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_nano_1507_);
lean_dec_ref(v___x_1505_);
v___x_1508_ = lean_int_neg(v_second_1503_);
lean_dec(v_second_1503_);
v___x_1509_ = lean_int_neg(v_nano_1504_);
lean_dec(v_nano_1504_);
v___x_1510_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1511_ = lean_int_mul(v_second_1506_, v___x_1510_);
lean_dec(v_second_1506_);
v_nanos_1512_ = lean_int_add(v___x_1511_, v_nano_1507_);
lean_dec(v_nano_1507_);
lean_dec(v___x_1511_);
v___x_1513_ = lean_int_mul(v___x_1508_, v___x_1510_);
lean_dec(v___x_1508_);
v_nanos_1514_ = lean_int_add(v___x_1513_, v___x_1509_);
lean_dec(v___x_1509_);
lean_dec(v___x_1513_);
v___x_1515_ = lean_int_add(v_nanos_1512_, v_nanos_1514_);
lean_dec(v_nanos_1514_);
lean_dec(v_nanos_1512_);
v___x_1516_ = l_Std_Time_Duration_ofNanoseconds(v___x_1515_);
lean_dec(v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object* v_pd_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1520_ = l_Std_Time_PlainDate_toEpochDay(v_pd_1519_);
v___x_1521_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1522_ = lean_int_mul(v___x_1520_, v___x_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object* v_wt_1525_){
_start:
{
lean_object* v_second_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_second_1526_ = lean_ctor_get(v_wt_1525_, 0);
v___x_1527_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1528_ = lean_int_div(v_second_1526_, v___x_1527_);
v___x_1529_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1528_);
lean_dec(v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object* v_wt_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Std_Time_PlainDate_ofWallTime(v_wt_1530_);
lean_dec_ref(v_wt_1530_);
return v_res_1531_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1533_ = lean_int_neg(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_1534_, lean_object* v_y_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_nanos_1546_; lean_object* v___x_1547_; lean_object* v_nanos_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1536_ = l_Std_Time_PlainDate_toEpochDay(v_x_1534_);
v___x_1537_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1538_ = lean_int_mul(v___x_1536_, v___x_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1540_ = l_Std_Time_PlainDate_toEpochDay(v_y_1535_);
v___x_1541_ = lean_int_mul(v___x_1540_, v___x_1537_);
lean_dec(v___x_1540_);
v___x_1542_ = lean_int_neg(v___x_1541_);
lean_dec(v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
v___x_1544_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1545_ = lean_int_mul(v___x_1538_, v___x_1544_);
lean_dec(v___x_1538_);
v_nanos_1546_ = lean_int_add(v___x_1545_, v___x_1539_);
lean_dec(v___x_1545_);
v___x_1547_ = lean_int_mul(v___x_1542_, v___x_1544_);
lean_dec(v___x_1542_);
v_nanos_1548_ = lean_int_add(v___x_1547_, v___x_1543_);
lean_dec(v___x_1547_);
v___x_1549_ = lean_int_add(v_nanos_1546_, v_nanos_1548_);
lean_dec(v_nanos_1548_);
lean_dec(v_nanos_1546_);
v___x_1550_ = l_Std_Time_Duration_ofNanoseconds(v___x_1549_);
lean_dec(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object* v_date_1553_, lean_object* v_time_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_date_1553_);
lean_ctor_set(v___x_1555_, 1, v_time_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object* v_pt_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1556_);
v___x_1558_ = l_Std_Time_Duration_ofNanoseconds(v___x_1557_);
lean_dec(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object* v_pt_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_Time_PlainTime_toWallTime(v_pt_1559_);
lean_dec_ref(v_pt_1559_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object* v_wt_1561_){
_start:
{
lean_object* v_second_1562_; lean_object* v_nano_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_nanos_1566_; lean_object* v___x_1567_; 
v_second_1562_ = lean_ctor_get(v_wt_1561_, 0);
v_nano_1563_ = lean_ctor_get(v_wt_1561_, 1);
v___x_1564_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1565_ = lean_int_mul(v_second_1562_, v___x_1564_);
v_nanos_1566_ = lean_int_add(v___x_1565_, v_nano_1563_);
lean_dec(v___x_1565_);
v___x_1567_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1566_);
lean_dec(v_nanos_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object* v_wt_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_Time_PlainTime_ofWallTime(v_wt_1568_);
lean_dec_ref(v_wt_1568_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object* v_time_1570_, lean_object* v_date_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_date_1571_);
lean_ctor_set(v___x_1572_, 1, v_time_1570_);
return v___x_1572_;
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
