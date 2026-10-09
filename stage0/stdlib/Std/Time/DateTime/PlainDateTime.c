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
uint8_t l_Std_Time_instDecidableEqPlainDateTime_decEq(lean_object* v_x_120_, lean_object* v_x_121_){
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
LEAN_EXPORT void l_Std_Time_instDecidableEqPlainDateTime_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_120_ = stack[0].m_obj;
lean_object* v_x_121_ = stack[1].m_obj;
uint8_t v_res_128_;
v_res_128_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_120_, v_x_121_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDateTime_decEq___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_129_, v_x_130_);
lean_dec_ref(v_x_130_);
lean_dec_ref(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
uint8_t l_Std_Time_instDecidableEqPlainDateTime(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqPlainDateTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_133_ = stack[0].m_obj;
lean_object* v_x_134_ = stack[1].m_obj;
uint8_t v_res_136_;
v_res_136_ = l_Std_Time_instDecidableEqPlainDateTime(v_x_133_, v_x_134_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDateTime___boxed(lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_Time_instDecidableEqPlainDateTime(v_x_137_, v_x_138_);
lean_dec_ref(v_x_138_);
lean_dec_ref(v_x_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(8u);
v___x_155_ = lean_nat_to_int(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0));
v___x_164_ = lean_string_length(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13, &l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once, _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13);
v___x_166_ = lean_nat_to_int(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr___redArg(lean_object* v_x_171_){
_start:
{
lean_object* v_date_172_; lean_object* v_time_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_205_; 
v_date_172_ = lean_ctor_get(v_x_171_, 0);
v_time_173_ = lean_ctor_get(v_x_171_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_205_ == 0)
{
v___x_175_ = v_x_171_;
v_isShared_176_ = v_isSharedCheck_205_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_time_173_);
lean_inc(v_date_172_);
lean_dec(v_x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_205_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_177_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5));
v___x_178_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6));
v___x_179_ = lean_obj_once(&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7, &l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7);
v___x_180_ = l_Std_Time_instReprPlainDate_repr___redArg(v_date_172_);
lean_dec_ref(v_date_172_);
if (v_isShared_176_ == 0)
{
lean_ctor_set_tag(v___x_175_, 4);
lean_ctor_set(v___x_175_, 1, v___x_180_);
lean_ctor_set(v___x_175_, 0, v___x_179_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_204_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_183_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_178_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9));
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_box(1);
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11));
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_177_);
v___x_193_ = l_Std_Time_instReprPlainTime_repr___redArg(v_time_173_);
lean_dec_ref(v_time_173_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_179_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_183_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_obj_once(&l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14, &l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14);
v___x_198_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15));
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_196_);
v___x_200_ = ((lean_object*)(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16));
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_197_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_183_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr(lean_object* v_x_206_, lean_object* v_prec_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_Time_instReprPlainDateTime_repr___redArg(v_x_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDateTime_repr___boxed(lean_object* v_x_209_, lean_object* v_prec_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Time_instReprPlainDateTime_repr(v_x_209_, v_prec_210_);
lean_dec(v_prec_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__0(lean_object* v_x_214_){
_start:
{
lean_object* v_date_215_; 
v_date_215_ = lean_ctor_get(v_x_214_, 0);
lean_inc_ref(v_date_215_);
return v_date_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__0___boxed(lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_Time_instOrdPlainDateTime___lam__0(v_x_216_);
lean_dec_ref(v_x_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__1(lean_object* v_x_218_){
_start:
{
lean_object* v_time_219_; 
v_time_219_ = lean_ctor_get(v_x_218_, 1);
lean_inc_ref(v_time_219_);
return v_time_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDateTime___lam__1___boxed(lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Time_instOrdPlainDateTime___lam__1(v_x_220_);
lean_dec_ref(v_x_220_);
return v_res_221_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime___closed__2(void){
_start:
{
lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___f_224_ = ((lean_object*)(l_Std_Time_instOrdPlainDateTime___closed__0));
v___x_225_ = l_Std_Time_instOrdPlainDate;
v___x_226_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, lean_box(0));
lean_closure_set(v___x_226_, 2, v___x_225_);
lean_closure_set(v___x_226_, 3, v___f_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime___closed__3(void){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___f_227_ = ((lean_object*)(l_Std_Time_instOrdPlainDateTime___closed__1));
v___x_228_ = l_Std_Time_instOrdPlainTime;
v___x_229_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v___x_228_);
lean_closure_set(v___x_229_, 3, v___f_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime___closed__4(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Std_Time_instOrdPlainDateTime___closed__3, &l_Std_Time_instOrdPlainDateTime___closed__3_once, _init_l_Std_Time_instOrdPlainDateTime___closed__3);
v___x_231_ = lean_obj_once(&l_Std_Time_instOrdPlainDateTime___closed__2, &l_Std_Time_instOrdPlainDateTime___closed__2_once, _init_l_Std_Time_instOrdPlainDateTime___closed__2);
v___x_232_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_232_, 0, lean_box(0));
lean_closure_set(v___x_232_, 1, lean_box(0));
lean_closure_set(v___x_232_, 2, v___x_231_);
lean_closure_set(v___x_232_, 3, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDateTime(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Std_Time_instOrdPlainDateTime___closed__4, &l_Std_Time_instOrdPlainDateTime___closed__4_once, _init_l_Std_Time_instOrdPlainDateTime___closed__4);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__1(lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Rat_ofInt(v_a_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(86400u);
v___x_237_ = lean_nat_to_int(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toWallTime___closed__1(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(1000000000u);
v___x_239_ = lean_nat_to_int(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object* v_dt_240_){
_start:
{
lean_object* v_time_241_; lean_object* v_date_242_; lean_object* v_nanosecond_243_; lean_object* v_days_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_nanos_251_; lean_object* v___x_252_; 
v_time_241_ = lean_ctor_get(v_dt_240_, 1);
lean_inc_ref(v_time_241_);
v_date_242_ = lean_ctor_get(v_dt_240_, 0);
lean_inc_ref(v_date_242_);
lean_dec_ref(v_dt_240_);
v_nanosecond_243_ = lean_ctor_get(v_time_241_, 3);
lean_inc(v_nanosecond_243_);
v_days_244_ = l_Std_Time_PlainDate_toEpochDay(v_date_242_);
v___x_245_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_246_ = lean_int_mul(v_days_244_, v___x_245_);
lean_dec(v_days_244_);
v___x_247_ = l_Std_Time_PlainTime_toSeconds(v_time_241_);
lean_dec_ref(v_time_241_);
v___x_248_ = lean_int_add(v___x_246_, v___x_247_);
lean_dec(v___x_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_250_ = lean_int_mul(v___x_248_, v___x_249_);
lean_dec(v___x_248_);
v_nanos_251_ = lean_int_add(v___x_250_, v_nanosecond_243_);
lean_dec(v_nanosecond_243_);
lean_dec(v___x_250_);
v___x_252_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_251_);
lean_dec(v_nanos_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__0(lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_nat_to_int(v_a_253_);
v___x_255_ = l_Rat_ofInt(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(lean_object* v_as_x27_256_, lean_object* v_b_257_){
_start:
{
if (lean_obj_tag(v_as_x27_256_) == 0)
{
return v_b_257_;
}
else
{
lean_object* v_head_258_; lean_object* v_tail_259_; lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_277_; 
v_head_258_ = lean_ctor_get(v_as_x27_256_, 0);
v_tail_259_ = lean_ctor_get(v_as_x27_256_, 1);
v_fst_260_ = lean_ctor_get(v_b_257_, 0);
v_snd_261_ = lean_ctor_get(v_b_257_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_b_257_);
if (v_isSharedCheck_277_ == 0)
{
v___x_263_ = v_b_257_;
v_isShared_264_ = v_isSharedCheck_277_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_snd_261_);
lean_inc(v_fst_260_);
lean_dec(v_b_257_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_277_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_unsigned_to_nat(13u);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = l_Fin_add(v___x_265_, v_snd_261_, v___x_266_);
lean_dec(v_snd_261_);
v___x_268_ = lean_int_dec_lt(v_fst_260_, v_head_258_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_int_sub(v_fst_260_, v_head_258_);
lean_dec(v_fst_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_267_);
lean_ctor_set(v___x_263_, 0, v___x_269_);
v___x_271_ = v___x_263_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_267_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v_as_x27_256_ = v_tail_259_;
v_b_257_ = v___x_271_;
goto _start;
}
}
else
{
lean_object* v___x_275_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_267_);
v___x_275_ = v___x_263_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_fst_260_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_267_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___boxed(lean_object* v_as_x27_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_278_, v_b_279_);
lean_dec(v_as_x27_278_);
return v_res_280_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_281_; lean_object* v_leapYearEpoch_282_; 
v___x_281_ = lean_unsigned_to_nat(11017u);
v_leapYearEpoch_282_ = lean_nat_to_int(v___x_281_);
return v_leapYearEpoch_282_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(365u);
v___x_284_ = lean_nat_to_int(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(400u);
v___x_286_ = lean_nat_to_int(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_288_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_289_ = lean_int_mul(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(97u);
v___x_291_ = lean_nat_to_int(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_daysPer400Y_294_; 
v___x_292_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__4, &l_Std_Time_PlainDateTime_ofWallTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4);
v___x_293_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__3, &l_Std_Time_PlainDateTime_ofWallTime___closed__3_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3);
v_daysPer400Y_294_ = lean_int_add(v___x_293_, v___x_292_);
return v_daysPer400Y_294_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(100u);
v___x_296_ = lean_nat_to_int(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_298_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_299_ = lean_int_mul(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(24u);
v___x_301_ = lean_nat_to_int(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_daysPer100Y_304_; 
v___x_302_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__8, &l_Std_Time_PlainDateTime_ofWallTime___closed__8_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8);
v___x_303_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__7, &l_Std_Time_PlainDateTime_ofWallTime___closed__7_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7);
v_daysPer100Y_304_ = lean_int_add(v___x_303_, v___x_302_);
return v_daysPer100Y_304_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(4u);
v___x_306_ = lean_nat_to_int(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_308_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_309_ = lean_int_mul(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_daysPer4Y_312_; 
v___x_310_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_311_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__11, &l_Std_Time_PlainDateTime_ofWallTime___closed__11_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11);
v_daysPer4Y_312_ = lean_int_add(v___x_311_, v___x_310_);
return v_daysPer4Y_312_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(60u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(3600u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(31u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(29u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_box(0);
v___x_322_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__16, &l_Std_Time_PlainDateTime_ofWallTime___closed__16_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__17, &l_Std_Time_PlainDateTime_ofWallTime___closed__17_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17);
v___x_325_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__18, &l_Std_Time_PlainDateTime_ofWallTime___closed__18_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18);
v___x_328_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__19, &l_Std_Time_PlainDateTime_ofWallTime___closed__19_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19);
v___x_331_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__20, &l_Std_Time_PlainDateTime_ofWallTime___closed__20_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20);
v___x_334_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__21, &l_Std_Time_PlainDateTime_ofWallTime___closed__21_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21);
v___x_337_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__22, &l_Std_Time_PlainDateTime_ofWallTime___closed__22_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22);
v___x_340_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__23, &l_Std_Time_PlainDateTime_ofWallTime___closed__23_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23);
v___x_343_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__24, &l_Std_Time_PlainDateTime_ofWallTime___closed__24_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24);
v___x_346_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__25, &l_Std_Time_PlainDateTime_ofWallTime___closed__25_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25);
v___x_349_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__26, &l_Std_Time_PlainDateTime_ofWallTime___closed__26_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26);
v___x_352_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
return v___x_353_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_months_356_; 
v___x_354_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__27, &l_Std_Time_PlainDateTime_ofWallTime___closed__27_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27);
v___x_355_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v_months_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_months_356_, 0, v___x_355_);
lean_ctor_set(v_months_356_, 1, v___x_354_);
return v_months_356_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(2000u);
v___x_358_ = lean_nat_to_int(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(25u);
v___x_360_ = lean_nat_to_int(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_362_ = lean_int_neg(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object* v_stamp_363_){
_start:
{
lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v_second_385_; lean_object* v_nano_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_533_; 
v_second_385_ = lean_ctor_get(v_stamp_363_, 0);
v_nano_386_ = lean_ctor_get(v_stamp_363_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_stamp_363_);
if (v_isSharedCheck_533_ == 0)
{
v___x_388_ = v_stamp_363_;
v_isShared_389_ = v_isSharedCheck_533_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_nano_386_);
lean_inc(v_second_385_);
lean_dec(v_stamp_363_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_533_;
goto v_resetjp_387_;
}
v___jp_364_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_370_, 0, v___y_368_);
lean_ctor_set(v___x_370_, 1, v___y_366_);
lean_ctor_set(v___x_370_, 2, v___y_365_);
lean_ctor_set(v___x_370_, 3, v___y_367_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___y_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
v___jp_372_:
{
lean_object* v_max_381_; uint8_t v___x_382_; 
v_max_381_ = l_Std_Time_Month_Ordinal_days(v___y_380_, v___y_378_);
v___x_382_ = lean_int_dec_lt(v_max_381_, v___y_379_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_max_381_);
v___x_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_383_, 0, v___y_377_);
lean_ctor_set(v___x_383_, 1, v___y_378_);
lean_ctor_set(v___x_383_, 2, v___y_379_);
v___y_365_ = v___y_373_;
v___y_366_ = v___y_374_;
v___y_367_ = v___y_375_;
v___y_368_ = v___y_376_;
v___y_369_ = v___x_383_;
goto v___jp_364_;
}
else
{
lean_object* v___x_384_; 
lean_dec(v___y_379_);
v___x_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_384_, 0, v___y_377_);
lean_ctor_set(v___x_384_, 1, v___y_378_);
lean_ctor_set(v___x_384_, 2, v_max_381_);
v___y_365_ = v___y_373_;
v___y_366_ = v___y_374_;
v___y_367_ = v___y_375_;
v___y_368_ = v___y_376_;
v___y_369_ = v___x_384_;
goto v___jp_364_;
}
}
v_resetjp_387_:
{
lean_object* v_leapYearEpoch_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_daysPer400Y_404_; lean_object* v___x_405_; lean_object* v_daysPer100Y_406_; lean_object* v___x_407_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_daysPer4Y_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v_hmon_432_; lean_object* v_year_433_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_remYears_450_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v_quadrennialCycles_485_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_centenialCycles_495_; lean_object* v___y_503_; lean_object* v_quadracentennialCycles_504_; lean_object* v_remDays_505_; lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v_snd_519_; lean_object* v_secs_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_leapYearEpoch_390_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__0, &l_Std_Time_PlainDateTime_ofWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0);
v___x_391_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_392_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v_daysPer400Y_404_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__5, &l_Std_Time_PlainDateTime_ofWallTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5);
v___x_405_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v_daysPer100Y_406_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__9, &l_Std_Time_PlainDateTime_ofWallTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9);
v___x_407_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v_daysPer4Y_424_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__12, &l_Std_Time_PlainDateTime_ofWallTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12);
v___x_425_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_426_ = lean_int_mul(v_second_385_, v___x_425_);
lean_dec(v_second_385_);
v___x_427_ = lean_int_add(v___x_426_, v_nano_386_);
lean_dec(v_nano_386_);
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
v___jp_393_:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_int_mod(v___y_399_, v___x_392_);
v___x_403_ = lean_int_dec_eq(v___x_402_, v___y_398_);
lean_dec(v___y_398_);
lean_dec(v___x_402_);
v___y_373_ = v___y_394_;
v___y_374_ = v___y_395_;
v___y_375_ = v___y_396_;
v___y_376_ = v___y_397_;
v___y_377_ = v___y_399_;
v___y_378_ = v___y_400_;
v___y_379_ = v___y_401_;
v___y_380_ = v___x_403_;
goto v___jp_372_;
}
v___jp_408_:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = lean_int_mod(v___y_414_, v___x_407_);
v___x_418_ = lean_nat_to_int(v___y_409_);
v___x_419_ = lean_int_dec_eq(v___x_417_, v___x_418_);
lean_dec(v___x_417_);
if (v___x_419_ == 0)
{
lean_dec(v___x_418_);
v___y_373_ = v___y_410_;
v___y_374_ = v___y_411_;
v___y_375_ = v___y_412_;
v___y_376_ = v___y_413_;
v___y_377_ = v___y_414_;
v___y_378_ = v___y_415_;
v___y_379_ = v___y_416_;
v___y_380_ = v___x_419_;
goto v___jp_372_;
}
else
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_int_mod(v___y_414_, v___x_405_);
v___x_421_ = lean_int_dec_eq(v___x_420_, v___x_418_);
lean_dec(v___x_420_);
if (v___x_421_ == 0)
{
if (v___x_419_ == 0)
{
v___y_394_ = v___y_410_;
v___y_395_ = v___y_411_;
v___y_396_ = v___y_412_;
v___y_397_ = v___y_413_;
v___y_398_ = v___x_418_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_416_;
goto v___jp_393_;
}
else
{
lean_dec(v___x_418_);
v___y_373_ = v___y_410_;
v___y_374_ = v___y_411_;
v___y_375_ = v___y_412_;
v___y_376_ = v___y_413_;
v___y_377_ = v___y_414_;
v___y_378_ = v___y_415_;
v___y_379_ = v___y_416_;
v___y_380_ = v___x_419_;
goto v___jp_372_;
}
}
else
{
v___y_394_ = v___y_410_;
v___y_395_ = v___y_411_;
v___y_396_ = v___y_412_;
v___y_397_ = v___y_413_;
v___y_398_ = v___x_418_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_416_;
goto v___jp_393_;
}
}
}
v___jp_428_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_434_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__13, &l_Std_Time_PlainDateTime_ofWallTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13);
v___x_435_ = lean_int_emod(v___y_431_, v___x_434_);
v___x_436_ = lean_int_ediv(v___y_431_, v___x_434_);
v___x_437_ = lean_int_emod(v___x_436_, v___x_434_);
lean_dec(v___x_436_);
v___x_438_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__14, &l_Std_Time_PlainDateTime_ofWallTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14);
v___x_439_ = lean_int_ediv(v___y_431_, v___x_438_);
lean_dec(v___y_431_);
v___x_440_ = lean_int_emod(v___x_427_, v___x_425_);
lean_dec(v___x_427_);
v___x_441_ = l_Fin_succ___redArg(v___y_430_);
lean_dec(v___y_430_);
v___x_442_ = lean_nat_dec_le(v___x_422_, v___x_441_);
if (v___x_442_ == 0)
{
lean_dec(v___x_441_);
v___y_409_ = v___y_429_;
v___y_410_ = v___x_435_;
v___y_411_ = v___x_437_;
v___y_412_ = v___x_440_;
v___y_413_ = v___x_439_;
v___y_414_ = v_year_433_;
v___y_415_ = v_hmon_432_;
v___y_416_ = v___x_423_;
goto v___jp_408_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_nat_to_int(v___x_441_);
v___y_409_ = v___y_429_;
v___y_410_ = v___x_435_;
v___y_411_ = v___x_437_;
v___y_412_ = v___x_440_;
v___y_413_ = v___x_439_;
v___y_414_ = v_year_433_;
v___y_415_ = v_hmon_432_;
v___y_416_ = v___x_443_;
goto v___jp_408_;
}
}
v___jp_444_:
{
lean_object* v___x_451_; lean_object* v_remDays_452_; lean_object* v___x_453_; lean_object* v_months_454_; lean_object* v_mon_455_; lean_object* v___x_457_; 
v___x_451_ = lean_int_mul(v_remYears_450_, v___x_391_);
v_remDays_452_ = lean_int_sub(v___y_449_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___y_449_);
v___x_453_ = lean_unsigned_to_nat(31u);
v_months_454_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__28, &l_Std_Time_PlainDateTime_ofWallTime___closed__28_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28);
v_mon_455_ = lean_unsigned_to_nat(0u);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_mon_455_);
lean_ctor_set(v___x_388_, 0, v_remDays_452_);
v___x_457_ = v___x_388_;
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
v___x_463_ = lean_int_mul(v___x_407_, v___y_448_);
lean_dec(v___y_448_);
v___x_464_ = lean_int_add(v___x_462_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_int_mul(v___x_405_, v___y_445_);
lean_dec(v___y_445_);
v___x_466_ = lean_int_add(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_int_mul(v___x_392_, v___y_447_);
lean_dec(v___y_447_);
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
v___y_429_ = v_mon_455_;
v___y_430_ = v___x_470_;
v___y_431_ = v___y_446_;
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
v___y_429_ = v_mon_455_;
v___y_430_ = v___x_470_;
v___y_431_ = v___y_446_;
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
v_remDays_487_ = lean_int_sub(v___y_482_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v___y_482_);
v_remYears_488_ = lean_int_ediv(v_remDays_487_, v___x_391_);
v___x_489_ = lean_int_dec_eq(v_remYears_488_, v___x_407_);
if (v___x_489_ == 0)
{
v___y_445_ = v___y_481_;
v___y_446_ = v___y_484_;
v___y_447_ = v___y_483_;
v___y_448_ = v_quadrennialCycles_485_;
v___y_449_ = v_remDays_487_;
v_remYears_450_ = v_remYears_488_;
goto v___jp_444_;
}
else
{
lean_object* v_remYears_490_; 
v_remYears_490_ = lean_int_sub(v_remYears_488_, v___x_423_);
lean_dec(v_remYears_488_);
v___y_445_ = v___y_481_;
v___y_446_ = v___y_484_;
v___y_447_ = v___y_483_;
v___y_448_ = v_quadrennialCycles_485_;
v___y_449_ = v_remDays_487_;
v_remYears_450_ = v_remYears_490_;
goto v___jp_444_;
}
}
v___jp_491_:
{
lean_object* v___x_496_; lean_object* v_remDays_497_; lean_object* v_quadrennialCycles_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_496_ = lean_int_mul(v_centenialCycles_495_, v_daysPer100Y_406_);
v_remDays_497_ = lean_int_sub(v___y_492_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v___y_492_);
v_quadrennialCycles_498_ = lean_int_ediv(v_remDays_497_, v_daysPer4Y_424_);
v___x_499_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__30, &l_Std_Time_PlainDateTime_ofWallTime___closed__30_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30);
v___x_500_ = lean_int_dec_eq(v_quadrennialCycles_498_, v___x_499_);
if (v___x_500_ == 0)
{
v___y_481_ = v_centenialCycles_495_;
v___y_482_ = v_remDays_497_;
v___y_483_ = v___y_494_;
v___y_484_ = v___y_493_;
v_quadrennialCycles_485_ = v_quadrennialCycles_498_;
goto v___jp_480_;
}
else
{
lean_object* v_quadrennialCycles_501_; 
v_quadrennialCycles_501_ = lean_int_sub(v_quadrennialCycles_498_, v___x_423_);
lean_dec(v_quadrennialCycles_498_);
v___y_481_ = v_centenialCycles_495_;
v___y_482_ = v_remDays_497_;
v___y_483_ = v___y_494_;
v___y_484_ = v___y_493_;
v_quadrennialCycles_485_ = v_quadrennialCycles_501_;
goto v___jp_480_;
}
}
v___jp_502_:
{
lean_object* v_centenialCycles_506_; uint8_t v___x_507_; 
v_centenialCycles_506_ = lean_int_ediv(v_remDays_505_, v_daysPer100Y_406_);
v___x_507_ = lean_int_dec_eq(v_centenialCycles_506_, v___x_407_);
if (v___x_507_ == 0)
{
v___y_492_ = v_remDays_505_;
v___y_493_ = v___y_503_;
v___y_494_ = v_quadracentennialCycles_504_;
v_centenialCycles_495_ = v_centenialCycles_506_;
goto v___jp_491_;
}
else
{
lean_object* v_centenialCycles_508_; 
v_centenialCycles_508_ = lean_int_sub(v_centenialCycles_506_, v___x_423_);
lean_dec(v_centenialCycles_506_);
v___y_492_ = v_remDays_505_;
v___y_493_ = v___y_503_;
v___y_494_ = v_quadracentennialCycles_504_;
v_centenialCycles_495_ = v_centenialCycles_508_;
goto v___jp_491_;
}
}
v___jp_509_:
{
lean_object* v_quadracentennialCycles_512_; lean_object* v_remDays_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_quadracentennialCycles_512_ = lean_int_ediv(v_snd_511_, v_daysPer400Y_404_);
v_remDays_513_ = lean_int_emod(v_snd_511_, v_daysPer400Y_404_);
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
v_remDays_516_ = lean_int_add(v_remDays_513_, v_daysPer400Y_404_);
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
v_rawDays_522_ = lean_int_sub(v_boundedDaysSinceEpoch_521_, v_leapYearEpoch_390_);
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
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_554_, uint8_t v_desiredWeekday_555_){
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
LEAN_EXPORT void l_Std_Time_PlainDateTime_withWeekday_0interp(lean_interpreter_value* stack)
{
lean_object* v_dt_554_ = stack[0].m_obj;
uint8_t v_desiredWeekday_555_ = stack[1].m_num;
lean_object* v_res_566_;
v_res_566_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_554_, v_desiredWeekday_555_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_567_, lean_object* v_desiredWeekday_568_){
_start:
{
uint8_t v_desiredWeekday_boxed_569_; lean_object* v_res_570_; 
v_desiredWeekday_boxed_569_ = lean_unbox(v_desiredWeekday_568_);
v_res_570_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_567_, v_desiredWeekday_boxed_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_571_, lean_object* v_days_572_){
_start:
{
lean_object* v_date_573_; lean_object* v_time_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_612_; 
v_date_573_ = lean_ctor_get(v_dt_571_, 0);
v_time_574_ = lean_ctor_get(v_dt_571_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_dt_571_);
if (v_isSharedCheck_612_ == 0)
{
v___x_576_ = v_dt_571_;
v_isShared_577_ = v_isSharedCheck_612_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_time_574_);
lean_inc(v_date_573_);
lean_dec(v_dt_571_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_612_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_year_578_; lean_object* v_month_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_610_; 
v_year_578_ = lean_ctor_get(v_date_573_, 0);
v_month_579_ = lean_ctor_get(v_date_573_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_date_573_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_date_573_, 2);
lean_dec(v_unused_611_);
v___x_581_ = v_date_573_;
v_isShared_582_ = v_isSharedCheck_610_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_month_579_);
lean_inc(v_year_578_);
lean_dec(v_date_573_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_610_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint8_t v___y_584_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_606_; 
v___x_599_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_600_ = lean_int_mod(v_year_578_, v___x_599_);
v___x_601_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_606_ = lean_int_dec_eq(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
if (v___x_606_ == 0)
{
v___y_584_ = v___x_606_;
goto v___jp_583_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_608_ = lean_int_mod(v_year_578_, v___x_607_);
v___x_609_ = lean_int_dec_eq(v___x_608_, v___x_601_);
lean_dec(v___x_608_);
if (v___x_609_ == 0)
{
if (v___x_606_ == 0)
{
goto v___jp_602_;
}
else
{
v___y_584_ = v___x_606_;
goto v___jp_583_;
}
}
else
{
goto v___jp_602_;
}
}
v___jp_583_:
{
lean_object* v_max_585_; uint8_t v___x_586_; 
v_max_585_ = l_Std_Time_Month_Ordinal_days(v___y_584_, v_month_579_);
v___x_586_ = lean_int_dec_lt(v_max_585_, v_days_572_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v_max_585_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v_days_572_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_year_578_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_month_579_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_days_572_);
v___x_588_ = v_reuseFailAlloc_592_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_588_);
v___x_590_ = v___x_576_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_time_574_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_object* v___x_594_; 
lean_dec(v_days_572_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v_max_585_);
v___x_594_ = v___x_581_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_year_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_month_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_max_585_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_594_);
v___x_596_ = v___x_576_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_time_574_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
v___jp_602_:
{
lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_604_ = lean_int_mod(v_year_578_, v___x_603_);
v___x_605_ = lean_int_dec_eq(v___x_604_, v___x_601_);
lean_dec(v___x_604_);
v___y_584_ = v___x_605_;
goto v___jp_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_613_, lean_object* v_days_614_){
_start:
{
lean_object* v_date_615_; lean_object* v_time_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_date_615_ = lean_ctor_get(v_dt_613_, 0);
v_time_616_ = lean_ctor_get(v_dt_613_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_dt_613_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v_dt_613_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_time_616_);
lean_inc(v_date_615_);
lean_dec(v_dt_613_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_year_620_; lean_object* v_month_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v_year_620_ = lean_ctor_get(v_date_615_, 0);
lean_inc(v_year_620_);
v_month_621_ = lean_ctor_get(v_date_615_, 1);
lean_inc(v_month_621_);
lean_dec_ref(v_date_615_);
v___x_622_ = l_Std_Time_PlainDate_rollOver(v_year_620_, v_month_621_, v_days_614_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_time_616_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_627_, lean_object* v_days_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_627_, v_days_628_);
lean_dec(v_days_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_630_, lean_object* v_month_631_){
_start:
{
lean_object* v_date_632_; lean_object* v_time_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_671_; 
v_date_632_ = lean_ctor_get(v_dt_630_, 0);
v_time_633_ = lean_ctor_get(v_dt_630_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_dt_630_);
if (v_isSharedCheck_671_ == 0)
{
v___x_635_ = v_dt_630_;
v_isShared_636_ = v_isSharedCheck_671_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_time_633_);
lean_inc(v_date_632_);
lean_dec(v_dt_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_671_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_year_637_; lean_object* v_day_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_669_; 
v_year_637_ = lean_ctor_get(v_date_632_, 0);
v_day_638_ = lean_ctor_get(v_date_632_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v_date_632_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_date_632_, 1);
lean_dec(v_unused_670_);
v___x_640_ = v_date_632_;
v_isShared_641_ = v_isSharedCheck_669_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_day_638_);
lean_inc(v_year_637_);
lean_dec(v_date_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_669_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___y_643_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_665_; 
v___x_658_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_659_ = lean_int_mod(v_year_637_, v___x_658_);
v___x_660_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_665_ = lean_int_dec_eq(v___x_659_, v___x_660_);
lean_dec(v___x_659_);
if (v___x_665_ == 0)
{
v___y_643_ = v___x_665_;
goto v___jp_642_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_667_ = lean_int_mod(v_year_637_, v___x_666_);
v___x_668_ = lean_int_dec_eq(v___x_667_, v___x_660_);
lean_dec(v___x_667_);
if (v___x_668_ == 0)
{
if (v___x_665_ == 0)
{
goto v___jp_661_;
}
else
{
v___y_643_ = v___x_665_;
goto v___jp_642_;
}
}
else
{
goto v___jp_661_;
}
}
v___jp_642_:
{
lean_object* v_max_644_; uint8_t v___x_645_; 
v_max_644_ = l_Std_Time_Month_Ordinal_days(v___y_643_, v_month_631_);
v___x_645_ = lean_int_dec_lt(v_max_644_, v_day_638_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v_max_644_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_month_631_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_year_637_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_month_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_day_638_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_647_);
v___x_649_ = v___x_635_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_time_633_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v_day_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v_max_644_);
lean_ctor_set(v___x_640_, 1, v_month_631_);
v___x_653_ = v___x_640_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_year_637_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_month_631_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_max_644_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_653_);
v___x_655_ = v___x_635_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_time_633_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
v___jp_661_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_663_ = lean_int_mod(v_year_637_, v___x_662_);
v___x_664_ = lean_int_dec_eq(v___x_663_, v___x_660_);
lean_dec(v___x_663_);
v___y_643_ = v___x_664_;
goto v___jp_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_672_, lean_object* v_month_673_){
_start:
{
lean_object* v_date_674_; lean_object* v_time_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_685_; 
v_date_674_ = lean_ctor_get(v_dt_672_, 0);
v_time_675_ = lean_ctor_get(v_dt_672_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_dt_672_);
if (v_isSharedCheck_685_ == 0)
{
v___x_677_ = v_dt_672_;
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_time_675_);
lean_inc(v_date_674_);
lean_dec(v_dt_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_year_679_; lean_object* v_day_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v_year_679_ = lean_ctor_get(v_date_674_, 0);
lean_inc(v_year_679_);
v_day_680_ = lean_ctor_get(v_date_674_, 2);
lean_inc(v_day_680_);
lean_dec_ref(v_date_674_);
v___x_681_ = l_Std_Time_PlainDate_rollOver(v_year_679_, v_month_673_, v_day_680_);
lean_dec(v_day_680_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_681_);
v___x_683_ = v___x_677_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_time_675_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_686_, lean_object* v_year_687_){
_start:
{
lean_object* v_date_688_; lean_object* v_time_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_727_; 
v_date_688_ = lean_ctor_get(v_dt_686_, 0);
v_time_689_ = lean_ctor_get(v_dt_686_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_dt_686_);
if (v_isSharedCheck_727_ == 0)
{
v___x_691_ = v_dt_686_;
v_isShared_692_ = v_isSharedCheck_727_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_time_689_);
lean_inc(v_date_688_);
lean_dec(v_dt_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_727_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_month_693_; lean_object* v_day_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_725_; 
v_month_693_ = lean_ctor_get(v_date_688_, 1);
v_day_694_ = lean_ctor_get(v_date_688_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_date_688_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_date_688_, 0);
lean_dec(v_unused_726_);
v___x_696_ = v_date_688_;
v_isShared_697_ = v_isSharedCheck_725_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_day_694_);
lean_inc(v_month_693_);
lean_dec(v_date_688_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_725_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint8_t v___y_699_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_721_; 
v___x_714_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_715_ = lean_int_mod(v_year_687_, v___x_714_);
v___x_716_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_721_ = lean_int_dec_eq(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
if (v___x_721_ == 0)
{
v___y_699_ = v___x_721_;
goto v___jp_698_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_723_ = lean_int_mod(v_year_687_, v___x_722_);
v___x_724_ = lean_int_dec_eq(v___x_723_, v___x_716_);
lean_dec(v___x_723_);
if (v___x_724_ == 0)
{
if (v___x_721_ == 0)
{
goto v___jp_717_;
}
else
{
v___y_699_ = v___x_721_;
goto v___jp_698_;
}
}
else
{
goto v___jp_717_;
}
}
v___jp_698_:
{
lean_object* v_max_700_; uint8_t v___x_701_; 
v_max_700_ = l_Std_Time_Month_Ordinal_days(v___y_699_, v_month_693_);
v___x_701_ = lean_int_dec_lt(v_max_700_, v_day_694_);
if (v___x_701_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v_max_700_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_year_687_);
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_year_687_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_month_693_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_day_694_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_703_);
v___x_705_ = v___x_691_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_time_689_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v___x_709_; 
lean_dec(v_day_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 2, v_max_700_);
lean_ctor_set(v___x_696_, 0, v_year_687_);
v___x_709_ = v___x_696_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_year_687_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_month_693_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_max_700_);
v___x_709_ = v_reuseFailAlloc_713_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_709_);
v___x_711_ = v___x_691_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_time_689_);
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
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_719_ = lean_int_mod(v_year_687_, v___x_718_);
v___x_720_ = lean_int_dec_eq(v___x_719_, v___x_716_);
lean_dec(v___x_719_);
v___y_699_ = v___x_720_;
goto v___jp_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_728_, lean_object* v_year_729_){
_start:
{
lean_object* v_date_730_; lean_object* v_time_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
v_date_730_ = lean_ctor_get(v_dt_728_, 0);
v_time_731_ = lean_ctor_get(v_dt_728_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_dt_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_733_ = v_dt_728_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_time_731_);
lean_inc(v_date_730_);
lean_dec(v_dt_728_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_month_735_; lean_object* v_day_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v_month_735_ = lean_ctor_get(v_date_730_, 1);
lean_inc(v_month_735_);
v_day_736_ = lean_ctor_get(v_date_730_, 2);
lean_inc(v_day_736_);
lean_dec_ref(v_date_730_);
v___x_737_ = l_Std_Time_PlainDate_rollOver(v_year_729_, v_month_735_, v_day_736_);
lean_dec(v_day_736_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_737_);
v___x_739_ = v___x_733_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_time_731_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_742_, lean_object* v_hour_743_){
_start:
{
lean_object* v_time_744_; lean_object* v_date_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_763_; 
v_time_744_ = lean_ctor_get(v_dt_742_, 1);
v_date_745_ = lean_ctor_get(v_dt_742_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_dt_742_);
if (v_isSharedCheck_763_ == 0)
{
v___x_747_ = v_dt_742_;
v_isShared_748_ = v_isSharedCheck_763_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_time_744_);
lean_inc(v_date_745_);
lean_dec(v_dt_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_763_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_minute_749_; lean_object* v_second_750_; lean_object* v_nanosecond_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_761_; 
v_minute_749_ = lean_ctor_get(v_time_744_, 1);
v_second_750_ = lean_ctor_get(v_time_744_, 2);
v_nanosecond_751_ = lean_ctor_get(v_time_744_, 3);
v_isSharedCheck_761_ = !lean_is_exclusive(v_time_744_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_time_744_, 0);
lean_dec(v_unused_762_);
v___x_753_ = v_time_744_;
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_nanosecond_751_);
lean_inc(v_second_750_);
lean_inc(v_minute_749_);
lean_dec(v_time_744_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_hour_743_);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_hour_743_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_minute_749_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_second_750_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_nanosecond_751_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_756_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_date_745_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_764_, lean_object* v_minute_765_){
_start:
{
lean_object* v_time_766_; lean_object* v_date_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_785_; 
v_time_766_ = lean_ctor_get(v_dt_764_, 1);
v_date_767_ = lean_ctor_get(v_dt_764_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_dt_764_);
if (v_isSharedCheck_785_ == 0)
{
v___x_769_ = v_dt_764_;
v_isShared_770_ = v_isSharedCheck_785_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_time_766_);
lean_inc(v_date_767_);
lean_dec(v_dt_764_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_785_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_hour_771_; lean_object* v_second_772_; lean_object* v_nanosecond_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_783_; 
v_hour_771_ = lean_ctor_get(v_time_766_, 0);
v_second_772_ = lean_ctor_get(v_time_766_, 2);
v_nanosecond_773_ = lean_ctor_get(v_time_766_, 3);
v_isSharedCheck_783_ = !lean_is_exclusive(v_time_766_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_time_766_, 1);
lean_dec(v_unused_784_);
v___x_775_ = v_time_766_;
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_nanosecond_773_);
lean_inc(v_second_772_);
lean_inc(v_hour_771_);
lean_dec(v_time_766_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_minute_765_);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_hour_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_minute_765_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_second_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_nanosecond_773_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v___x_778_);
v___x_780_ = v___x_769_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_date_767_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_786_, lean_object* v_second_787_){
_start:
{
lean_object* v_time_788_; lean_object* v_date_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_807_; 
v_time_788_ = lean_ctor_get(v_dt_786_, 1);
v_date_789_ = lean_ctor_get(v_dt_786_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_dt_786_);
if (v_isSharedCheck_807_ == 0)
{
v___x_791_ = v_dt_786_;
v_isShared_792_ = v_isSharedCheck_807_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_time_788_);
lean_inc(v_date_789_);
lean_dec(v_dt_786_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_807_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_hour_793_; lean_object* v_minute_794_; lean_object* v_nanosecond_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_805_; 
v_hour_793_ = lean_ctor_get(v_time_788_, 0);
v_minute_794_ = lean_ctor_get(v_time_788_, 1);
v_nanosecond_795_ = lean_ctor_get(v_time_788_, 3);
v_isSharedCheck_805_ = !lean_is_exclusive(v_time_788_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v_time_788_, 2);
lean_dec(v_unused_806_);
v___x_797_ = v_time_788_;
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_nanosecond_795_);
lean_inc(v_minute_794_);
lean_inc(v_hour_793_);
lean_dec(v_time_788_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 2, v_second_787_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_hour_793_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_minute_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_second_787_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_nanosecond_795_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_800_);
v___x_802_ = v___x_791_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_date_789_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(1000u);
v___x_809_ = lean_nat_to_int(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(1000000u);
v___x_811_ = lean_nat_to_int(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_812_, lean_object* v_millis_813_){
_start:
{
lean_object* v_time_814_; lean_object* v_date_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_838_; 
v_time_814_ = lean_ctor_get(v_dt_812_, 1);
v_date_815_ = lean_ctor_get(v_dt_812_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_dt_812_);
if (v_isSharedCheck_838_ == 0)
{
v___x_817_ = v_dt_812_;
v_isShared_818_ = v_isSharedCheck_838_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_time_814_);
lean_inc(v_date_815_);
lean_dec(v_dt_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_838_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_hour_819_; lean_object* v_minute_820_; lean_object* v_second_821_; lean_object* v_nanosecond_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_837_; 
v_hour_819_ = lean_ctor_get(v_time_814_, 0);
v_minute_820_ = lean_ctor_get(v_time_814_, 1);
v_second_821_ = lean_ctor_get(v_time_814_, 2);
v_nanosecond_822_ = lean_ctor_get(v_time_814_, 3);
v_isSharedCheck_837_ = !lean_is_exclusive(v_time_814_);
if (v_isSharedCheck_837_ == 0)
{
v___x_824_ = v_time_814_;
v_isShared_825_ = v_isSharedCheck_837_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_nanosecond_822_);
lean_inc(v_second_821_);
lean_inc(v_minute_820_);
lean_inc(v_hour_819_);
lean_dec(v_time_814_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_837_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_826_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_827_ = lean_int_emod(v_nanosecond_822_, v___x_826_);
lean_dec(v_nanosecond_822_);
v___x_828_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_829_ = lean_int_mul(v_millis_813_, v___x_828_);
v___x_830_ = lean_int_add(v___x_829_, v___x_827_);
lean_dec(v___x_827_);
lean_dec(v___x_829_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 3, v___x_830_);
v___x_832_ = v___x_824_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_hour_819_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_minute_820_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_second_821_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v___x_830_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_834_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_832_);
v___x_834_ = v___x_817_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_date_815_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_839_, lean_object* v_millis_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_839_, v_millis_840_);
lean_dec(v_millis_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_842_, lean_object* v_nano_843_){
_start:
{
lean_object* v_time_844_; lean_object* v_date_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_863_; 
v_time_844_ = lean_ctor_get(v_dt_842_, 1);
v_date_845_ = lean_ctor_get(v_dt_842_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_dt_842_);
if (v_isSharedCheck_863_ == 0)
{
v___x_847_ = v_dt_842_;
v_isShared_848_ = v_isSharedCheck_863_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_time_844_);
lean_inc(v_date_845_);
lean_dec(v_dt_842_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_863_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_hour_849_; lean_object* v_minute_850_; lean_object* v_second_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_861_; 
v_hour_849_ = lean_ctor_get(v_time_844_, 0);
v_minute_850_ = lean_ctor_get(v_time_844_, 1);
v_second_851_ = lean_ctor_get(v_time_844_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_time_844_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_time_844_, 3);
lean_dec(v_unused_862_);
v___x_853_ = v_time_844_;
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_second_851_);
lean_inc(v_minute_850_);
lean_inc(v_hour_849_);
lean_dec(v_time_844_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 3, v_nano_843_);
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_hour_849_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_minute_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_second_851_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_nano_843_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_856_);
v___x_858_ = v___x_847_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_date_845_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_864_, lean_object* v_days_865_){
_start:
{
lean_object* v_date_866_; lean_object* v_time_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_877_; 
v_date_866_ = lean_ctor_get(v_dt_864_, 0);
v_time_867_ = lean_ctor_get(v_dt_864_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_dt_864_);
if (v_isSharedCheck_877_ == 0)
{
v___x_869_ = v_dt_864_;
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_time_867_);
lean_inc(v_date_866_);
lean_dec(v_dt_864_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_dateDays_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v_dateDays_871_ = l_Std_Time_PlainDate_toEpochDay(v_date_866_);
v___x_872_ = lean_int_add(v_dateDays_871_, v_days_865_);
lean_dec(v_dateDays_871_);
v___x_873_ = l_Std_Time_PlainDate_ofEpochDay(v___x_872_);
lean_dec(v___x_872_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_time_867_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_878_, lean_object* v_days_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_Time_PlainDateTime_addDays(v_dt_878_, v_days_879_);
lean_dec(v_days_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_881_, lean_object* v_days_882_){
_start:
{
lean_object* v_date_883_; lean_object* v_time_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_895_; 
v_date_883_ = lean_ctor_get(v_dt_881_, 0);
v_time_884_ = lean_ctor_get(v_dt_881_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_dt_881_);
if (v_isSharedCheck_895_ == 0)
{
v___x_886_ = v_dt_881_;
v_isShared_887_ = v_isSharedCheck_895_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_time_884_);
lean_inc(v_date_883_);
lean_dec(v_dt_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_895_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v_dateDays_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_888_ = lean_int_neg(v_days_882_);
v_dateDays_889_ = l_Std_Time_PlainDate_toEpochDay(v_date_883_);
v___x_890_ = lean_int_add(v_dateDays_889_, v___x_888_);
lean_dec(v___x_888_);
lean_dec(v_dateDays_889_);
v___x_891_ = l_Std_Time_PlainDate_ofEpochDay(v___x_890_);
lean_dec(v___x_890_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_891_);
v___x_893_ = v___x_886_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_time_884_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_896_, lean_object* v_days_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Std_Time_PlainDateTime_subDays(v_dt_896_, v_days_897_);
lean_dec(v_days_897_);
return v_res_898_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(7u);
v___x_900_ = lean_nat_to_int(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_901_, lean_object* v_weeks_902_){
_start:
{
lean_object* v_date_903_; lean_object* v_time_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_916_; 
v_date_903_ = lean_ctor_get(v_dt_901_, 0);
v_time_904_ = lean_ctor_get(v_dt_901_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_dt_901_);
if (v_isSharedCheck_916_ == 0)
{
v___x_906_ = v_dt_901_;
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_time_904_);
lean_inc(v_date_903_);
lean_dec(v_dt_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_dateDays_908_; lean_object* v___x_909_; lean_object* v_daysToAdd_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v_dateDays_908_ = l_Std_Time_PlainDate_toEpochDay(v_date_903_);
v___x_909_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_910_ = lean_int_mul(v_weeks_902_, v___x_909_);
v___x_911_ = lean_int_add(v_dateDays_908_, v_daysToAdd_910_);
lean_dec(v_daysToAdd_910_);
lean_dec(v_dateDays_908_);
v___x_912_ = l_Std_Time_PlainDate_ofEpochDay(v___x_911_);
lean_dec(v___x_911_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_912_);
v___x_914_ = v___x_906_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_time_904_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_917_, lean_object* v_weeks_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_917_, v_weeks_918_);
lean_dec(v_weeks_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_920_, lean_object* v_weeks_921_){
_start:
{
lean_object* v_date_922_; lean_object* v_time_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_936_; 
v_date_922_ = lean_ctor_get(v_dt_920_, 0);
v_time_923_ = lean_ctor_get(v_dt_920_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_dt_920_);
if (v_isSharedCheck_936_ == 0)
{
v___x_925_ = v_dt_920_;
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_time_923_);
lean_inc(v_date_922_);
lean_dec(v_dt_920_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v_dateDays_928_; lean_object* v___x_929_; lean_object* v_daysToAdd_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_927_ = lean_int_neg(v_weeks_921_);
v_dateDays_928_ = l_Std_Time_PlainDate_toEpochDay(v_date_922_);
v___x_929_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_930_ = lean_int_mul(v___x_927_, v___x_929_);
lean_dec(v___x_927_);
v___x_931_ = lean_int_add(v_dateDays_928_, v_daysToAdd_930_);
lean_dec(v_daysToAdd_930_);
lean_dec(v_dateDays_928_);
v___x_932_ = l_Std_Time_PlainDate_ofEpochDay(v___x_931_);
lean_dec(v___x_931_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_932_);
v___x_934_ = v___x_925_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_time_923_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_937_, lean_object* v_weeks_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_937_, v_weeks_938_);
lean_dec(v_weeks_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_940_, lean_object* v_months_941_){
_start:
{
lean_object* v_date_942_; lean_object* v_time_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v_date_942_ = lean_ctor_get(v_dt_940_, 0);
v_time_943_ = lean_ctor_get(v_dt_940_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_dt_940_);
if (v_isSharedCheck_951_ == 0)
{
v___x_945_ = v_dt_940_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_time_943_);
lean_inc(v_date_942_);
lean_dec(v_dt_940_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = l_Std_Time_PlainDate_addMonthsClip(v_date_942_, v_months_941_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_time_943_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_952_, lean_object* v_months_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_952_, v_months_953_);
lean_dec(v_months_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_955_, lean_object* v_months_956_){
_start:
{
lean_object* v_date_957_; lean_object* v_time_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_967_; 
v_date_957_ = lean_ctor_get(v_dt_955_, 0);
v_time_958_ = lean_ctor_get(v_dt_955_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_dt_955_);
if (v_isSharedCheck_967_ == 0)
{
v___x_960_ = v_dt_955_;
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_time_958_);
lean_inc(v_date_957_);
lean_dec(v_dt_955_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_962_ = lean_int_neg(v_months_956_);
v___x_963_ = l_Std_Time_PlainDate_addMonthsClip(v_date_957_, v___x_962_);
lean_dec(v___x_962_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_963_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_time_958_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_968_, lean_object* v_months_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_968_, v_months_969_);
lean_dec(v_months_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_971_, lean_object* v_months_972_){
_start:
{
lean_object* v_date_973_; lean_object* v_time_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_date_973_ = lean_ctor_get(v_dt_971_, 0);
v_time_974_ = lean_ctor_get(v_dt_971_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_dt_971_);
if (v_isSharedCheck_982_ == 0)
{
v___x_976_ = v_dt_971_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_time_974_);
lean_inc(v_date_973_);
lean_dec(v_dt_971_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_973_, v_months_972_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_time_974_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_983_, lean_object* v_months_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_983_, v_months_984_);
lean_dec(v_months_984_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_986_, lean_object* v_months_987_){
_start:
{
lean_object* v_date_988_; lean_object* v_time_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v_date_988_ = lean_ctor_get(v_dt_986_, 0);
v_time_989_ = lean_ctor_get(v_dt_986_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_dt_986_);
if (v_isSharedCheck_998_ == 0)
{
v___x_991_ = v_dt_986_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_time_989_);
lean_inc(v_date_988_);
lean_dec(v_dt_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_993_ = lean_int_neg(v_months_987_);
v___x_994_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_988_, v___x_993_);
lean_dec(v___x_993_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_time_989_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_999_, lean_object* v_months_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_999_, v_months_1000_);
lean_dec(v_months_1000_);
return v_res_1001_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(12u);
v___x_1003_ = lean_nat_to_int(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_1004_, lean_object* v_years_1005_){
_start:
{
lean_object* v_date_1006_; lean_object* v_time_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1017_; 
v_date_1006_ = lean_ctor_get(v_dt_1004_, 0);
v_time_1007_ = lean_ctor_get(v_dt_1004_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_dt_1004_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1009_ = v_dt_1004_;
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_time_1007_);
lean_inc(v_date_1006_);
lean_dec(v_dt_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1017_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1011_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1012_ = lean_int_mul(v_years_1005_, v___x_1011_);
v___x_1013_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1006_, v___x_1012_);
lean_dec(v___x_1012_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_time_1007_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_1018_, lean_object* v_years_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_1018_, v_years_1019_);
lean_dec(v_years_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_1021_, lean_object* v_years_1022_){
_start:
{
lean_object* v_date_1023_; lean_object* v_time_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
v_date_1023_ = lean_ctor_get(v_dt_1021_, 0);
v_time_1024_ = lean_ctor_get(v_dt_1021_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_dt_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1026_ = v_dt_1021_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_time_1024_);
lean_inc(v_date_1023_);
lean_dec(v_dt_1021_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1028_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1029_ = lean_int_mul(v_years_1022_, v___x_1028_);
v___x_1030_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1023_, v___x_1029_);
lean_dec(v___x_1029_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1030_);
v___x_1032_ = v___x_1026_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_time_1024_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_1035_, lean_object* v_years_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_1035_, v_years_1036_);
lean_dec(v_years_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_1038_, lean_object* v_years_1039_){
_start:
{
lean_object* v_date_1040_; lean_object* v_time_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1052_; 
v_date_1040_ = lean_ctor_get(v_dt_1038_, 0);
v_time_1041_ = lean_ctor_get(v_dt_1038_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_dt_1038_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1043_ = v_dt_1038_;
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_time_1041_);
lean_inc(v_date_1040_);
lean_dec(v_dt_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1045_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1046_ = lean_int_mul(v_years_1039_, v___x_1045_);
v___x_1047_ = lean_int_neg(v___x_1046_);
lean_dec(v___x_1046_);
v___x_1048_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1040_, v___x_1047_);
lean_dec(v___x_1047_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1048_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_time_1041_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_1053_, lean_object* v_years_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_1053_, v_years_1054_);
lean_dec(v_years_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_1056_, lean_object* v_years_1057_){
_start:
{
lean_object* v_date_1058_; lean_object* v_time_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1070_; 
v_date_1058_ = lean_ctor_get(v_dt_1056_, 0);
v_time_1059_ = lean_ctor_get(v_dt_1056_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_dt_1056_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1061_ = v_dt_1056_;
v_isShared_1062_ = v_isSharedCheck_1070_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_time_1059_);
lean_inc(v_date_1058_);
lean_dec(v_dt_1056_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1070_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1063_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1064_ = lean_int_mul(v_years_1057_, v___x_1063_);
v___x_1065_ = lean_int_neg(v___x_1064_);
lean_dec(v___x_1064_);
v___x_1066_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1058_, v___x_1065_);
lean_dec(v___x_1065_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1066_);
v___x_1068_ = v___x_1061_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_time_1059_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_1071_, lean_object* v_years_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_1071_, v_years_1072_);
lean_dec(v_years_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_1074_, lean_object* v_nanos_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v_second_1077_; lean_object* v_nano_1078_; lean_object* v___x_1079_; lean_object* v_second_1080_; lean_object* v_nano_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_nanos_1084_; lean_object* v___x_1085_; lean_object* v_nanos_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1076_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1074_);
v_second_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_second_1077_);
v_nano_1078_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_nano_1078_);
lean_dec_ref(v___x_1076_);
v___x_1079_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1075_);
v_second_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_second_1080_);
v_nano_1081_ = lean_ctor_get(v___x_1079_, 1);
lean_inc(v_nano_1081_);
lean_dec_ref(v___x_1079_);
v___x_1082_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1083_ = lean_int_mul(v_second_1077_, v___x_1082_);
lean_dec(v_second_1077_);
v_nanos_1084_ = lean_int_add(v___x_1083_, v_nano_1078_);
lean_dec(v_nano_1078_);
lean_dec(v___x_1083_);
v___x_1085_ = lean_int_mul(v_second_1080_, v___x_1082_);
lean_dec(v_second_1080_);
v_nanos_1086_ = lean_int_add(v___x_1085_, v_nano_1081_);
lean_dec(v_nano_1081_);
lean_dec(v___x_1085_);
v___x_1087_ = lean_int_add(v_nanos_1084_, v_nanos_1086_);
lean_dec(v_nanos_1086_);
lean_dec(v_nanos_1084_);
v___x_1088_ = l_Std_Time_Duration_ofNanoseconds(v___x_1087_);
lean_dec(v___x_1087_);
v___x_1089_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_1090_, lean_object* v_nanos_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_1090_, v_nanos_1091_);
lean_dec(v_nanos_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_1093_, lean_object* v_nanos_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v_second_1096_; lean_object* v_nano_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_second_1100_; lean_object* v_nano_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_nanos_1104_; lean_object* v___x_1105_; lean_object* v_nanos_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1095_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1093_);
v_second_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_second_1096_);
v_nano_1097_ = lean_ctor_get(v___x_1095_, 1);
lean_inc(v_nano_1097_);
lean_dec_ref(v___x_1095_);
v___x_1098_ = lean_int_neg(v_nanos_1094_);
v___x_1099_ = l_Std_Time_Duration_ofNanoseconds(v___x_1098_);
lean_dec(v___x_1098_);
v_second_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_second_1100_);
v_nano_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_nano_1101_);
lean_dec_ref(v___x_1099_);
v___x_1102_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1103_ = lean_int_mul(v_second_1096_, v___x_1102_);
lean_dec(v_second_1096_);
v_nanos_1104_ = lean_int_add(v___x_1103_, v_nano_1097_);
lean_dec(v_nano_1097_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_int_mul(v_second_1100_, v___x_1102_);
lean_dec(v_second_1100_);
v_nanos_1106_ = lean_int_add(v___x_1105_, v_nano_1101_);
lean_dec(v_nano_1101_);
lean_dec(v___x_1105_);
v___x_1107_ = lean_int_add(v_nanos_1104_, v_nanos_1106_);
lean_dec(v_nanos_1106_);
lean_dec(v_nanos_1104_);
v___x_1108_ = l_Std_Time_Duration_ofNanoseconds(v___x_1107_);
lean_dec(v___x_1107_);
v___x_1109_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_1110_, lean_object* v_nanos_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_1110_, v_nanos_1111_);
lean_dec(v_nanos_1111_);
return v_res_1112_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_cstr_to_nat("3600000000000");
v___x_1114_ = lean_nat_to_int(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_1115_, lean_object* v_hours_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v_second_1118_; lean_object* v_nano_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_second_1123_; lean_object* v_nano_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_nanos_1127_; lean_object* v___x_1128_; lean_object* v_nanos_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1117_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1115_);
v_second_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_second_1118_);
v_nano_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_nano_1119_);
lean_dec_ref(v___x_1117_);
v___x_1120_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1121_ = lean_int_mul(v_hours_1116_, v___x_1120_);
v___x_1122_ = l_Std_Time_Duration_ofNanoseconds(v___x_1121_);
lean_dec(v___x_1121_);
v_second_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_second_1123_);
v_nano_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_nano_1124_);
lean_dec_ref(v___x_1122_);
v___x_1125_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1126_ = lean_int_mul(v_second_1118_, v___x_1125_);
lean_dec(v_second_1118_);
v_nanos_1127_ = lean_int_add(v___x_1126_, v_nano_1119_);
lean_dec(v_nano_1119_);
lean_dec(v___x_1126_);
v___x_1128_ = lean_int_mul(v_second_1123_, v___x_1125_);
lean_dec(v_second_1123_);
v_nanos_1129_ = lean_int_add(v___x_1128_, v_nano_1124_);
lean_dec(v_nano_1124_);
lean_dec(v___x_1128_);
v___x_1130_ = lean_int_add(v_nanos_1127_, v_nanos_1129_);
lean_dec(v_nanos_1129_);
lean_dec(v_nanos_1127_);
v___x_1131_ = l_Std_Time_Duration_ofNanoseconds(v___x_1130_);
lean_dec(v___x_1130_);
v___x_1132_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_1133_, lean_object* v_hours_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_Time_PlainDateTime_addHours(v_dt_1133_, v_hours_1134_);
lean_dec(v_hours_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_1136_, lean_object* v_hours_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v_second_1139_; lean_object* v_nano_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_second_1145_; lean_object* v_nano_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_nanos_1149_; lean_object* v___x_1150_; lean_object* v_nanos_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1138_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1136_);
v_second_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_second_1139_);
v_nano_1140_ = lean_ctor_get(v___x_1138_, 1);
lean_inc(v_nano_1140_);
lean_dec_ref(v___x_1138_);
v___x_1141_ = lean_int_neg(v_hours_1137_);
v___x_1142_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1143_ = lean_int_mul(v___x_1141_, v___x_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = l_Std_Time_Duration_ofNanoseconds(v___x_1143_);
lean_dec(v___x_1143_);
v_second_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_second_1145_);
v_nano_1146_ = lean_ctor_get(v___x_1144_, 1);
lean_inc(v_nano_1146_);
lean_dec_ref(v___x_1144_);
v___x_1147_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1148_ = lean_int_mul(v_second_1139_, v___x_1147_);
lean_dec(v_second_1139_);
v_nanos_1149_ = lean_int_add(v___x_1148_, v_nano_1140_);
lean_dec(v_nano_1140_);
lean_dec(v___x_1148_);
v___x_1150_ = lean_int_mul(v_second_1145_, v___x_1147_);
lean_dec(v_second_1145_);
v_nanos_1151_ = lean_int_add(v___x_1150_, v_nano_1146_);
lean_dec(v_nano_1146_);
lean_dec(v___x_1150_);
v___x_1152_ = lean_int_add(v_nanos_1149_, v_nanos_1151_);
lean_dec(v_nanos_1151_);
lean_dec(v_nanos_1149_);
v___x_1153_ = l_Std_Time_Duration_ofNanoseconds(v___x_1152_);
lean_dec(v___x_1152_);
v___x_1154_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_1155_, lean_object* v_hours_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_Time_PlainDateTime_subHours(v_dt_1155_, v_hours_1156_);
lean_dec(v_hours_1156_);
return v_res_1157_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_cstr_to_nat("60000000000");
v___x_1159_ = lean_nat_to_int(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_1160_, lean_object* v_minutes_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v_second_1163_; lean_object* v_nano_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_second_1168_; lean_object* v_nano_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_nanos_1172_; lean_object* v___x_1173_; lean_object* v_nanos_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1162_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1160_);
v_second_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_second_1163_);
v_nano_1164_ = lean_ctor_get(v___x_1162_, 1);
lean_inc(v_nano_1164_);
lean_dec_ref(v___x_1162_);
v___x_1165_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1166_ = lean_int_mul(v_minutes_1161_, v___x_1165_);
v___x_1167_ = l_Std_Time_Duration_ofNanoseconds(v___x_1166_);
lean_dec(v___x_1166_);
v_second_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_second_1168_);
v_nano_1169_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_nano_1169_);
lean_dec_ref(v___x_1167_);
v___x_1170_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1171_ = lean_int_mul(v_second_1163_, v___x_1170_);
lean_dec(v_second_1163_);
v_nanos_1172_ = lean_int_add(v___x_1171_, v_nano_1164_);
lean_dec(v_nano_1164_);
lean_dec(v___x_1171_);
v___x_1173_ = lean_int_mul(v_second_1168_, v___x_1170_);
lean_dec(v_second_1168_);
v_nanos_1174_ = lean_int_add(v___x_1173_, v_nano_1169_);
lean_dec(v_nano_1169_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_int_add(v_nanos_1172_, v_nanos_1174_);
lean_dec(v_nanos_1174_);
lean_dec(v_nanos_1172_);
v___x_1176_ = l_Std_Time_Duration_ofNanoseconds(v___x_1175_);
lean_dec(v___x_1175_);
v___x_1177_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_1178_, lean_object* v_minutes_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_1178_, v_minutes_1179_);
lean_dec(v_minutes_1179_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_1181_, lean_object* v_minutes_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v_second_1184_; lean_object* v_nano_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_second_1190_; lean_object* v_nano_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_nanos_1194_; lean_object* v___x_1195_; lean_object* v_nanos_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1183_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1181_);
v_second_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_second_1184_);
v_nano_1185_ = lean_ctor_get(v___x_1183_, 1);
lean_inc(v_nano_1185_);
lean_dec_ref(v___x_1183_);
v___x_1186_ = lean_int_neg(v_minutes_1182_);
v___x_1187_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1188_ = lean_int_mul(v___x_1186_, v___x_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = l_Std_Time_Duration_ofNanoseconds(v___x_1188_);
lean_dec(v___x_1188_);
v_second_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_second_1190_);
v_nano_1191_ = lean_ctor_get(v___x_1189_, 1);
lean_inc(v_nano_1191_);
lean_dec_ref(v___x_1189_);
v___x_1192_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1193_ = lean_int_mul(v_second_1184_, v___x_1192_);
lean_dec(v_second_1184_);
v_nanos_1194_ = lean_int_add(v___x_1193_, v_nano_1185_);
lean_dec(v_nano_1185_);
lean_dec(v___x_1193_);
v___x_1195_ = lean_int_mul(v_second_1190_, v___x_1192_);
lean_dec(v_second_1190_);
v_nanos_1196_ = lean_int_add(v___x_1195_, v_nano_1191_);
lean_dec(v_nano_1191_);
lean_dec(v___x_1195_);
v___x_1197_ = lean_int_add(v_nanos_1194_, v_nanos_1196_);
lean_dec(v_nanos_1196_);
lean_dec(v_nanos_1194_);
v___x_1198_ = l_Std_Time_Duration_ofNanoseconds(v___x_1197_);
lean_dec(v___x_1197_);
v___x_1199_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_1200_, lean_object* v_minutes_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_1200_, v_minutes_1201_);
lean_dec(v_minutes_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_1203_, lean_object* v_seconds_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v_second_1206_; lean_object* v_nano_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_second_1211_; lean_object* v_nano_1212_; lean_object* v___x_1213_; lean_object* v_nanos_1214_; lean_object* v___x_1215_; lean_object* v_nanos_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1205_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1203_);
v_second_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_second_1206_);
v_nano_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_nano_1207_);
lean_dec_ref(v___x_1205_);
v___x_1208_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1209_ = lean_int_mul(v_seconds_1204_, v___x_1208_);
v___x_1210_ = l_Std_Time_Duration_ofNanoseconds(v___x_1209_);
lean_dec(v___x_1209_);
v_second_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_second_1211_);
v_nano_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_nano_1212_);
lean_dec_ref(v___x_1210_);
v___x_1213_ = lean_int_mul(v_second_1206_, v___x_1208_);
lean_dec(v_second_1206_);
v_nanos_1214_ = lean_int_add(v___x_1213_, v_nano_1207_);
lean_dec(v_nano_1207_);
lean_dec(v___x_1213_);
v___x_1215_ = lean_int_mul(v_second_1211_, v___x_1208_);
lean_dec(v_second_1211_);
v_nanos_1216_ = lean_int_add(v___x_1215_, v_nano_1212_);
lean_dec(v_nano_1212_);
lean_dec(v___x_1215_);
v___x_1217_ = lean_int_add(v_nanos_1214_, v_nanos_1216_);
lean_dec(v_nanos_1216_);
lean_dec(v_nanos_1214_);
v___x_1218_ = l_Std_Time_Duration_ofNanoseconds(v___x_1217_);
lean_dec(v___x_1217_);
v___x_1219_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_1220_, lean_object* v_seconds_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_1220_, v_seconds_1221_);
lean_dec(v_seconds_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_1223_, lean_object* v_seconds_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v_second_1226_; lean_object* v_nano_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_second_1232_; lean_object* v_nano_1233_; lean_object* v___x_1234_; lean_object* v_nanos_1235_; lean_object* v___x_1236_; lean_object* v_nanos_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1225_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1223_);
v_second_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_second_1226_);
v_nano_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_nano_1227_);
lean_dec_ref(v___x_1225_);
v___x_1228_ = lean_int_neg(v_seconds_1224_);
v___x_1229_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1230_ = lean_int_mul(v___x_1228_, v___x_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = l_Std_Time_Duration_ofNanoseconds(v___x_1230_);
lean_dec(v___x_1230_);
v_second_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_second_1232_);
v_nano_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_nano_1233_);
lean_dec_ref(v___x_1231_);
v___x_1234_ = lean_int_mul(v_second_1226_, v___x_1229_);
lean_dec(v_second_1226_);
v_nanos_1235_ = lean_int_add(v___x_1234_, v_nano_1227_);
lean_dec(v_nano_1227_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_int_mul(v_second_1232_, v___x_1229_);
lean_dec(v_second_1232_);
v_nanos_1237_ = lean_int_add(v___x_1236_, v_nano_1233_);
lean_dec(v_nano_1233_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_int_add(v_nanos_1235_, v_nanos_1237_);
lean_dec(v_nanos_1237_);
lean_dec(v_nanos_1235_);
v___x_1239_ = l_Std_Time_Duration_ofNanoseconds(v___x_1238_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_1241_, lean_object* v_seconds_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_1241_, v_seconds_1242_);
lean_dec(v_seconds_1242_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_1244_, lean_object* v_milliseconds_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v_second_1247_; lean_object* v_nano_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_second_1252_; lean_object* v_nano_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_nanos_1256_; lean_object* v___x_1257_; lean_object* v_nanos_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1246_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1244_);
v_second_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_second_1247_);
v_nano_1248_ = lean_ctor_get(v___x_1246_, 1);
lean_inc(v_nano_1248_);
lean_dec_ref(v___x_1246_);
v___x_1249_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1250_ = lean_int_mul(v_milliseconds_1245_, v___x_1249_);
v___x_1251_ = l_Std_Time_Duration_ofNanoseconds(v___x_1250_);
lean_dec(v___x_1250_);
v_second_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_second_1252_);
v_nano_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_nano_1253_);
lean_dec_ref(v___x_1251_);
v___x_1254_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1255_ = lean_int_mul(v_second_1247_, v___x_1254_);
lean_dec(v_second_1247_);
v_nanos_1256_ = lean_int_add(v___x_1255_, v_nano_1248_);
lean_dec(v_nano_1248_);
lean_dec(v___x_1255_);
v___x_1257_ = lean_int_mul(v_second_1252_, v___x_1254_);
lean_dec(v_second_1252_);
v_nanos_1258_ = lean_int_add(v___x_1257_, v_nano_1253_);
lean_dec(v_nano_1253_);
lean_dec(v___x_1257_);
v___x_1259_ = lean_int_add(v_nanos_1256_, v_nanos_1258_);
lean_dec(v_nanos_1258_);
lean_dec(v_nanos_1256_);
v___x_1260_ = l_Std_Time_Duration_ofNanoseconds(v___x_1259_);
lean_dec(v___x_1259_);
v___x_1261_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_1262_, lean_object* v_milliseconds_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_1262_, v_milliseconds_1263_);
lean_dec(v_milliseconds_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_1265_, lean_object* v_milliseconds_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v_second_1268_; lean_object* v_nano_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_second_1274_; lean_object* v_nano_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_nanos_1278_; lean_object* v___x_1279_; lean_object* v_nanos_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1267_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1265_);
v_second_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_second_1268_);
v_nano_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_nano_1269_);
lean_dec_ref(v___x_1267_);
v___x_1270_ = lean_int_neg(v_milliseconds_1266_);
v___x_1271_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1272_ = lean_int_mul(v___x_1270_, v___x_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = l_Std_Time_Duration_ofNanoseconds(v___x_1272_);
lean_dec(v___x_1272_);
v_second_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_second_1274_);
v_nano_1275_ = lean_ctor_get(v___x_1273_, 1);
lean_inc(v_nano_1275_);
lean_dec_ref(v___x_1273_);
v___x_1276_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1277_ = lean_int_mul(v_second_1268_, v___x_1276_);
lean_dec(v_second_1268_);
v_nanos_1278_ = lean_int_add(v___x_1277_, v_nano_1269_);
lean_dec(v_nano_1269_);
lean_dec(v___x_1277_);
v___x_1279_ = lean_int_mul(v_second_1274_, v___x_1276_);
lean_dec(v_second_1274_);
v_nanos_1280_ = lean_int_add(v___x_1279_, v_nano_1275_);
lean_dec(v_nano_1275_);
lean_dec(v___x_1279_);
v___x_1281_ = lean_int_add(v_nanos_1278_, v_nanos_1280_);
lean_dec(v_nanos_1280_);
lean_dec(v_nanos_1278_);
v___x_1282_ = l_Std_Time_Duration_ofNanoseconds(v___x_1281_);
lean_dec(v___x_1281_);
v___x_1283_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1284_, lean_object* v_milliseconds_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1284_, v_milliseconds_1285_);
lean_dec(v_milliseconds_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1287_){
_start:
{
lean_object* v_date_1288_; lean_object* v_year_1289_; 
v_date_1288_ = lean_ctor_get(v_dt_1287_, 0);
v_year_1289_ = lean_ctor_get(v_date_1288_, 0);
lean_inc(v_year_1289_);
return v_year_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_Time_PlainDateTime_year(v_dt_1290_);
lean_dec_ref(v_dt_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1292_){
_start:
{
lean_object* v_date_1293_; lean_object* v_month_1294_; 
v_date_1293_ = lean_ctor_get(v_dt_1292_, 0);
v_month_1294_ = lean_ctor_get(v_date_1293_, 1);
lean_inc(v_month_1294_);
return v_month_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_Time_PlainDateTime_month(v_dt_1295_);
lean_dec_ref(v_dt_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1297_){
_start:
{
lean_object* v_date_1298_; lean_object* v_day_1299_; 
v_date_1298_ = lean_ctor_get(v_dt_1297_, 0);
v_day_1299_ = lean_ctor_get(v_date_1298_, 2);
lean_inc(v_day_1299_);
return v_day_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_Time_PlainDateTime_day(v_dt_1300_);
lean_dec_ref(v_dt_1300_);
return v_res_1301_;
}
}
uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1302_){
_start:
{
lean_object* v_date_1303_; uint8_t v___x_1304_; 
v_date_1303_ = lean_ctor_get(v_dt_1302_, 0);
lean_inc_ref(v_date_1303_);
lean_dec_ref(v_dt_1302_);
v___x_1304_ = l_Std_Time_PlainDate_weekday(v_date_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT void l_Std_Time_PlainDateTime_weekday_0interp(lean_interpreter_value* stack)
{
lean_object* v_dt_1302_ = stack[0].m_obj;
uint8_t v_res_1305_;
v_res_1305_ = l_Std_Time_PlainDateTime_weekday(v_dt_1302_);
stack->m_num = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1306_){
_start:
{
uint8_t v_res_1307_; lean_object* v_r_1308_; 
v_res_1307_ = l_Std_Time_PlainDateTime_weekday(v_dt_1306_);
v_r_1308_ = lean_box(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1309_){
_start:
{
lean_object* v_time_1310_; lean_object* v_hour_1311_; 
v_time_1310_ = lean_ctor_get(v_dt_1309_, 1);
v_hour_1311_ = lean_ctor_get(v_time_1310_, 0);
lean_inc(v_hour_1311_);
return v_hour_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_Time_PlainDateTime_hour(v_dt_1312_);
lean_dec_ref(v_dt_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1314_){
_start:
{
lean_object* v_time_1315_; lean_object* v_minute_1316_; 
v_time_1315_ = lean_ctor_get(v_dt_1314_, 1);
v_minute_1316_ = lean_ctor_get(v_time_1315_, 1);
lean_inc(v_minute_1316_);
return v_minute_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_Time_PlainDateTime_minute(v_dt_1317_);
lean_dec_ref(v_dt_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1319_){
_start:
{
lean_object* v_time_1320_; lean_object* v_nanosecond_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_time_1320_ = lean_ctor_get(v_dt_1319_, 1);
v_nanosecond_1321_ = lean_ctor_get(v_time_1320_, 3);
v___x_1322_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1323_ = lean_int_ediv(v_nanosecond_1321_, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1324_);
lean_dec_ref(v_dt_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1326_){
_start:
{
lean_object* v_time_1327_; lean_object* v_second_1328_; 
v_time_1327_ = lean_ctor_get(v_dt_1326_, 1);
v_second_1328_ = lean_ctor_get(v_time_1327_, 2);
lean_inc(v_second_1328_);
return v_second_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_Time_PlainDateTime_second(v_dt_1329_);
lean_dec_ref(v_dt_1329_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1331_){
_start:
{
lean_object* v_time_1332_; lean_object* v_nanosecond_1333_; 
v_time_1332_ = lean_ctor_get(v_dt_1331_, 1);
v_nanosecond_1333_ = lean_ctor_get(v_time_1332_, 3);
lean_inc(v_nanosecond_1333_);
return v_nanosecond_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1334_);
lean_dec_ref(v_dt_1334_);
return v_res_1335_;
}
}
uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1336_){
_start:
{
lean_object* v_date_1337_; lean_object* v_year_1338_; uint8_t v___x_1339_; 
v_date_1337_ = lean_ctor_get(v_date_1336_, 0);
v_year_1338_ = lean_ctor_get(v_date_1337_, 0);
v___x_1339_ = l_Std_Time_Year_Offset_era(v_year_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT void l_Std_Time_PlainDateTime_era_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1336_ = stack[0].m_obj;
uint8_t v_res_1340_;
v_res_1340_ = l_Std_Time_PlainDateTime_era(v_date_1336_);
stack->m_num = v_res_1340_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1341_){
_start:
{
uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = l_Std_Time_PlainDateTime_era(v_date_1341_);
lean_dec_ref(v_date_1341_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1344_){
_start:
{
lean_object* v_date_1345_; lean_object* v_year_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1354_; 
v_date_1345_ = lean_ctor_get(v_date_1344_, 0);
v_year_1346_ = lean_ctor_get(v_date_1345_, 0);
v___x_1347_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1348_ = lean_int_mod(v_year_1346_, v___x_1347_);
v___x_1349_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1354_ = lean_int_dec_eq(v___x_1348_, v___x_1349_);
lean_dec(v___x_1348_);
if (v___x_1354_ == 0)
{
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1356_ = lean_int_mod(v_year_1346_, v___x_1355_);
v___x_1357_ = lean_int_dec_eq(v___x_1356_, v___x_1349_);
lean_dec(v___x_1356_);
if (v___x_1357_ == 0)
{
if (v___x_1354_ == 0)
{
goto v___jp_1350_;
}
else
{
return v___x_1354_;
}
}
else
{
goto v___jp_1350_;
}
}
v___jp_1350_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1351_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1352_ = lean_int_mod(v_year_1346_, v___x_1351_);
v___x_1353_ = lean_int_dec_eq(v___x_1352_, v___x_1349_);
lean_dec(v___x_1352_);
return v___x_1353_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDateTime_inLeapYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1344_ = stack[0].m_obj;
uint8_t v_res_1358_;
v_res_1358_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1344_);
stack->m_num = v_res_1358_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object* v_date_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1359_);
lean_dec_ref(v_date_1359_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1362_, uint8_t v_firstDay_1363_, lean_object* v_minDays_1364_){
_start:
{
lean_object* v_date_1365_; lean_object* v___x_1366_; 
v_date_1365_ = lean_ctor_get(v_date_1362_, 0);
lean_inc_ref(v_date_1365_);
lean_dec_ref(v_date_1362_);
v___x_1366_ = l_Std_Time_PlainDate_weekOfYear(v_date_1365_, v_firstDay_1363_, v_minDays_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT void l_Std_Time_PlainDateTime_weekOfYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1362_ = stack[0].m_obj;
uint8_t v_firstDay_1363_ = stack[1].m_num;
lean_object* v_minDays_1364_ = stack[2].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_1362_, v_firstDay_1363_, v_minDays_1364_);
stack->m_obj
 = v_res_1367_;
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
lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object* v_date_1373_, uint8_t v_firstDay_1374_, lean_object* v_minDays_1375_){
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
LEAN_EXPORT void l_Std_Time_PlainDateTime_weekYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1373_ = stack[0].m_obj;
uint8_t v_firstDay_1374_ = stack[1].m_num;
lean_object* v_minDays_1375_ = stack[2].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_Std_Time_PlainDateTime_weekYear(v_date_1373_, v_firstDay_1374_, v_minDays_1375_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object* v_date_1379_, lean_object* v_firstDay_1380_, lean_object* v_minDays_1381_){
_start:
{
uint8_t v_firstDay_boxed_1382_; lean_object* v_res_1383_; 
v_firstDay_boxed_1382_ = lean_unbox(v_firstDay_1380_);
v_res_1383_ = l_Std_Time_PlainDateTime_weekYear(v_date_1379_, v_firstDay_boxed_1382_, v_minDays_1381_);
lean_dec(v_minDays_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1384_){
_start:
{
lean_object* v_date_1385_; lean_object* v___x_1386_; 
v_date_1385_ = lean_ctor_get(v_date_1384_, 0);
v___x_1386_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1387_);
lean_dec_ref(v_date_1387_);
return v_res_1388_;
}
}
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1389_, uint8_t v_firstDay_1390_){
_start:
{
lean_object* v_date_1391_; lean_object* v___x_1392_; 
v_date_1391_ = lean_ctor_get(v_date_1389_, 0);
lean_inc_ref(v_date_1391_);
lean_dec_ref(v_date_1389_);
v___x_1392_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1391_, v_firstDay_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT void l_Std_Time_PlainDateTime_weekOfMonth_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1389_ = stack[0].m_obj;
uint8_t v_firstDay_1390_ = stack[1].m_num;
lean_object* v_res_1393_;
v_res_1393_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1389_, v_firstDay_1390_);
stack->m_obj
 = v_res_1393_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1394_, lean_object* v_firstDay_1395_){
_start:
{
uint8_t v_firstDay_boxed_1396_; lean_object* v_res_1397_; 
v_firstDay_boxed_1396_ = lean_unbox(v_firstDay_1395_);
v_res_1397_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1394_, v_firstDay_boxed_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1398_){
_start:
{
lean_object* v_date_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1423_; 
v_date_1399_ = lean_ctor_get(v_date_1398_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_date_1398_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_date_1398_, 1);
lean_dec(v_unused_1424_);
v___x_1401_ = v_date_1398_;
v_isShared_1402_ = v_isSharedCheck_1423_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_date_1399_);
lean_dec(v_date_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1423_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_year_1403_; lean_object* v_month_1404_; lean_object* v_day_1405_; uint8_t v___y_1407_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1419_; 
v_year_1403_ = lean_ctor_get(v_date_1399_, 0);
lean_inc(v_year_1403_);
v_month_1404_ = lean_ctor_get(v_date_1399_, 1);
lean_inc(v_month_1404_);
v_day_1405_ = lean_ctor_get(v_date_1399_, 2);
lean_inc(v_day_1405_);
lean_dec_ref(v_date_1399_);
v___x_1412_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1413_ = lean_int_mod(v_year_1403_, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1419_ = lean_int_dec_eq(v___x_1413_, v___x_1414_);
lean_dec(v___x_1413_);
if (v___x_1419_ == 0)
{
lean_dec(v_year_1403_);
v___y_1407_ = v___x_1419_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1421_ = lean_int_mod(v_year_1403_, v___x_1420_);
v___x_1422_ = lean_int_dec_eq(v___x_1421_, v___x_1414_);
lean_dec(v___x_1421_);
if (v___x_1422_ == 0)
{
if (v___x_1419_ == 0)
{
goto v___jp_1415_;
}
else
{
lean_dec(v_year_1403_);
v___y_1407_ = v___x_1419_;
goto v___jp_1406_;
}
}
else
{
goto v___jp_1415_;
}
}
v___jp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_day_1405_);
lean_ctor_set(v___x_1401_, 0, v_month_1404_);
v___x_1409_ = v___x_1401_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_month_1404_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_day_1405_);
v___x_1409_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Std_Time_ValidDate_dayOfYear(v___y_1407_, v___x_1409_);
lean_dec_ref(v___x_1409_);
return v___x_1410_;
}
}
v___jp_1415_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1417_ = lean_int_mod(v_year_1403_, v___x_1416_);
lean_dec(v_year_1403_);
v___x_1418_ = lean_int_dec_eq(v___x_1417_, v___x_1414_);
lean_dec(v___x_1417_);
v___y_1407_ = v___x_1418_;
goto v___jp_1406_;
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
