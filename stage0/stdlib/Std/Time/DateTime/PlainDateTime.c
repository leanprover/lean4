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
lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; lean_object* v_second_383_; lean_object* v_nano_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_522_; 
v_second_383_ = lean_ctor_get(v_stamp_361_, 0);
v_nano_384_ = lean_ctor_get(v_stamp_361_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_stamp_361_);
if (v_isSharedCheck_522_ == 0)
{
v___x_386_ = v_stamp_361_;
v_isShared_387_ = v_isSharedCheck_522_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_nano_384_);
lean_inc(v_second_383_);
lean_dec(v_stamp_361_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_522_;
goto v_resetjp_385_;
}
v___jp_362_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v___y_366_);
lean_ctor_set(v___x_368_, 1, v___y_364_);
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
v_max_379_ = l_Std_Time_Month_Ordinal_days(v___y_378_, v___y_376_);
v___x_380_ = lean_int_dec_lt(v_max_379_, v___y_377_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_max_379_);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v___y_375_);
lean_ctor_set(v___x_381_, 1, v___y_376_);
lean_ctor_set(v___x_381_, 2, v___y_377_);
v___y_363_ = v___y_371_;
v___y_364_ = v___y_372_;
v___y_365_ = v___y_373_;
v___y_366_ = v___y_374_;
v___y_367_ = v___x_381_;
goto v___jp_362_;
}
else
{
lean_object* v___x_382_; 
lean_dec(v___y_377_);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v___y_375_);
lean_ctor_set(v___x_382_, 1, v___y_376_);
lean_ctor_set(v___x_382_, 2, v_max_379_);
v___y_363_ = v___y_371_;
v___y_364_ = v___y_372_;
v___y_365_ = v___y_373_;
v___y_366_ = v___y_374_;
v___y_367_ = v___x_382_;
goto v___jp_362_;
}
}
v_resetjp_385_:
{
lean_object* v_leapYearEpoch_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_daysPer400Y_391_; lean_object* v___x_392_; lean_object* v_daysPer100Y_393_; lean_object* v___x_394_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_daysPer4Y_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v_hmon_421_; lean_object* v_year_422_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v_remYears_439_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v_quadrennialCycles_474_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v_centenialCycles_484_; lean_object* v___y_492_; lean_object* v_quadracentennialCycles_493_; lean_object* v_remDays_494_; lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v_snd_508_; lean_object* v_secs_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_leapYearEpoch_388_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__0, &l_Std_Time_PlainDateTime_ofWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0);
v___x_389_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_390_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v_daysPer400Y_391_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__5, &l_Std_Time_PlainDateTime_ofWallTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5);
v___x_392_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v_daysPer100Y_393_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__9, &l_Std_Time_PlainDateTime_ofWallTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9);
v___x_394_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v_daysPer4Y_413_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__12, &l_Std_Time_PlainDateTime_ofWallTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12);
v___x_414_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_415_ = lean_int_mul(v_second_383_, v___x_414_);
lean_dec(v_second_383_);
v___x_416_ = lean_int_add(v___x_415_, v_nano_384_);
lean_dec(v_nano_384_);
lean_dec(v___x_415_);
v_secs_517_ = lean_int_div(v___x_416_, v___x_414_);
v___x_518_ = lean_int_mod(v___x_416_, v___x_414_);
v___x_519_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_520_ = lean_int_dec_lt(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
if (v___x_520_ == 0)
{
v_snd_508_ = v_secs_517_;
goto v___jp_507_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_int_sub(v_secs_517_, v___x_412_);
lean_dec(v_secs_517_);
v_snd_508_ = v___x_521_;
goto v___jp_507_;
}
v___jp_395_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_int_mod(v___y_401_, v___x_394_);
v___x_405_ = lean_nat_to_int(v___y_396_);
v___x_406_ = lean_int_dec_eq(v___x_404_, v___x_405_);
lean_dec(v___x_404_);
if (v___x_406_ == 0)
{
lean_dec(v___x_405_);
v___y_371_ = v___y_397_;
v___y_372_ = v___y_398_;
v___y_373_ = v___y_399_;
v___y_374_ = v___y_400_;
v___y_375_ = v___y_401_;
v___y_376_ = v___y_402_;
v___y_377_ = v___y_403_;
v___y_378_ = v___x_406_;
goto v___jp_370_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_int_mod(v___y_401_, v___x_392_);
v___x_408_ = lean_int_dec_eq(v___x_407_, v___x_405_);
lean_dec(v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v___x_405_);
v___y_371_ = v___y_397_;
v___y_372_ = v___y_398_;
v___y_373_ = v___y_399_;
v___y_374_ = v___y_400_;
v___y_375_ = v___y_401_;
v___y_376_ = v___y_402_;
v___y_377_ = v___y_403_;
v___y_378_ = v___x_406_;
goto v___jp_370_;
}
else
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_int_mod(v___y_401_, v___x_390_);
v___x_410_ = lean_int_dec_eq(v___x_409_, v___x_405_);
lean_dec(v___x_405_);
lean_dec(v___x_409_);
v___y_371_ = v___y_397_;
v___y_372_ = v___y_398_;
v___y_373_ = v___y_399_;
v___y_374_ = v___y_400_;
v___y_375_ = v___y_401_;
v___y_376_ = v___y_402_;
v___y_377_ = v___y_403_;
v___y_378_ = v___x_410_;
goto v___jp_370_;
}
}
}
v___jp_417_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_423_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__13, &l_Std_Time_PlainDateTime_ofWallTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13);
v___x_424_ = lean_int_emod(v___y_420_, v___x_423_);
v___x_425_ = lean_int_ediv(v___y_420_, v___x_423_);
v___x_426_ = lean_int_emod(v___x_425_, v___x_423_);
lean_dec(v___x_425_);
v___x_427_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__14, &l_Std_Time_PlainDateTime_ofWallTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14);
v___x_428_ = lean_int_ediv(v___y_420_, v___x_427_);
lean_dec(v___y_420_);
v___x_429_ = lean_int_emod(v___x_416_, v___x_414_);
lean_dec(v___x_416_);
v___x_430_ = l_Fin_succ___redArg(v___y_419_);
lean_dec(v___y_419_);
v___x_431_ = lean_nat_dec_le(v___x_411_, v___x_430_);
if (v___x_431_ == 0)
{
lean_dec(v___x_430_);
v___y_396_ = v___y_418_;
v___y_397_ = v___x_424_;
v___y_398_ = v___x_426_;
v___y_399_ = v___x_429_;
v___y_400_ = v___x_428_;
v___y_401_ = v_year_422_;
v___y_402_ = v_hmon_421_;
v___y_403_ = v___x_412_;
goto v___jp_395_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = lean_nat_to_int(v___x_430_);
v___y_396_ = v___y_418_;
v___y_397_ = v___x_424_;
v___y_398_ = v___x_426_;
v___y_399_ = v___x_429_;
v___y_400_ = v___x_428_;
v___y_401_ = v_year_422_;
v___y_402_ = v_hmon_421_;
v___y_403_ = v___x_432_;
goto v___jp_395_;
}
}
v___jp_433_:
{
lean_object* v___x_440_; lean_object* v_remDays_441_; lean_object* v___x_442_; lean_object* v_months_443_; lean_object* v_mon_444_; lean_object* v___x_446_; 
v___x_440_ = lean_int_mul(v_remYears_439_, v___x_389_);
v_remDays_441_ = lean_int_sub(v___y_438_, v___x_440_);
lean_dec(v___x_440_);
lean_dec(v___y_438_);
v___x_442_ = lean_unsigned_to_nat(31u);
v_months_443_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__28, &l_Std_Time_PlainDateTime_ofWallTime___closed__28_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28);
v_mon_444_ = lean_unsigned_to_nat(0u);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_mon_444_);
lean_ctor_set(v___x_386_, 0, v_remDays_441_);
v___x_446_ = v___x_386_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_remDays_441_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_mon_444_);
v___x_446_ = v_reuseFailAlloc_468_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_year_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_447_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_months_443_, v___x_446_);
v_fst_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_fst_448_);
v_snd_449_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_snd_449_);
lean_dec_ref(v___x_447_);
v___x_450_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__29, &l_Std_Time_PlainDateTime_ofWallTime___closed__29_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29);
v___x_451_ = lean_int_add(v___x_450_, v_remYears_439_);
lean_dec(v_remYears_439_);
v___x_452_ = lean_int_mul(v___x_394_, v___y_437_);
lean_dec(v___y_437_);
v___x_453_ = lean_int_add(v___x_451_, v___x_452_);
lean_dec(v___x_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_int_mul(v___x_392_, v___y_434_);
lean_dec(v___y_434_);
v___x_455_ = lean_int_add(v___x_453_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_int_mul(v___x_390_, v___y_436_);
lean_dec(v___y_436_);
v_year_457_ = lean_int_add(v___x_455_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_455_);
v___x_458_ = l_Int_toNat(v_fst_448_);
lean_dec(v_fst_448_);
v___x_459_ = lean_nat_mod(v___x_458_, v___x_442_);
lean_dec(v___x_458_);
v___x_460_ = lean_unsigned_to_nat(10u);
v___x_461_ = lean_nat_dec_lt(v___x_460_, v_snd_449_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_unsigned_to_nat(2u);
v___x_463_ = lean_nat_add(v_snd_449_, v___x_462_);
lean_dec(v_snd_449_);
v___x_464_ = lean_nat_to_int(v___x_463_);
v___y_418_ = v_mon_444_;
v___y_419_ = v___x_459_;
v___y_420_ = v___y_435_;
v_hmon_421_ = v___x_464_;
v_year_422_ = v_year_457_;
goto v___jp_417_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_int_add(v_year_457_, v___x_412_);
lean_dec(v_year_457_);
v___x_466_ = lean_nat_sub(v_snd_449_, v___x_460_);
lean_dec(v_snd_449_);
v___x_467_ = lean_nat_to_int(v___x_466_);
v___y_418_ = v_mon_444_;
v___y_419_ = v___x_459_;
v___y_420_ = v___y_435_;
v_hmon_421_ = v___x_467_;
v_year_422_ = v___x_465_;
goto v___jp_417_;
}
}
}
v___jp_469_:
{
lean_object* v___x_475_; lean_object* v_remDays_476_; lean_object* v_remYears_477_; uint8_t v___x_478_; 
v___x_475_ = lean_int_mul(v_quadrennialCycles_474_, v_daysPer4Y_413_);
v_remDays_476_ = lean_int_sub(v___y_471_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v___y_471_);
v_remYears_477_ = lean_int_ediv(v_remDays_476_, v___x_389_);
v___x_478_ = lean_int_dec_eq(v_remYears_477_, v___x_394_);
if (v___x_478_ == 0)
{
v___y_434_ = v___y_470_;
v___y_435_ = v___y_473_;
v___y_436_ = v___y_472_;
v___y_437_ = v_quadrennialCycles_474_;
v___y_438_ = v_remDays_476_;
v_remYears_439_ = v_remYears_477_;
goto v___jp_433_;
}
else
{
lean_object* v_remYears_479_; 
v_remYears_479_ = lean_int_sub(v_remYears_477_, v___x_412_);
lean_dec(v_remYears_477_);
v___y_434_ = v___y_470_;
v___y_435_ = v___y_473_;
v___y_436_ = v___y_472_;
v___y_437_ = v_quadrennialCycles_474_;
v___y_438_ = v_remDays_476_;
v_remYears_439_ = v_remYears_479_;
goto v___jp_433_;
}
}
v___jp_480_:
{
lean_object* v___x_485_; lean_object* v_remDays_486_; lean_object* v_quadrennialCycles_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_485_ = lean_int_mul(v_centenialCycles_484_, v_daysPer100Y_393_);
v_remDays_486_ = lean_int_sub(v___y_481_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v___y_481_);
v_quadrennialCycles_487_ = lean_int_ediv(v_remDays_486_, v_daysPer4Y_413_);
v___x_488_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__30, &l_Std_Time_PlainDateTime_ofWallTime___closed__30_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30);
v___x_489_ = lean_int_dec_eq(v_quadrennialCycles_487_, v___x_488_);
if (v___x_489_ == 0)
{
v___y_470_ = v_centenialCycles_484_;
v___y_471_ = v_remDays_486_;
v___y_472_ = v___y_483_;
v___y_473_ = v___y_482_;
v_quadrennialCycles_474_ = v_quadrennialCycles_487_;
goto v___jp_469_;
}
else
{
lean_object* v_quadrennialCycles_490_; 
v_quadrennialCycles_490_ = lean_int_sub(v_quadrennialCycles_487_, v___x_412_);
lean_dec(v_quadrennialCycles_487_);
v___y_470_ = v_centenialCycles_484_;
v___y_471_ = v_remDays_486_;
v___y_472_ = v___y_483_;
v___y_473_ = v___y_482_;
v_quadrennialCycles_474_ = v_quadrennialCycles_490_;
goto v___jp_469_;
}
}
v___jp_491_:
{
lean_object* v_centenialCycles_495_; uint8_t v___x_496_; 
v_centenialCycles_495_ = lean_int_ediv(v_remDays_494_, v_daysPer100Y_393_);
v___x_496_ = lean_int_dec_eq(v_centenialCycles_495_, v___x_394_);
if (v___x_496_ == 0)
{
v___y_481_ = v_remDays_494_;
v___y_482_ = v___y_492_;
v___y_483_ = v_quadracentennialCycles_493_;
v_centenialCycles_484_ = v_centenialCycles_495_;
goto v___jp_480_;
}
else
{
lean_object* v_centenialCycles_497_; 
v_centenialCycles_497_ = lean_int_sub(v_centenialCycles_495_, v___x_412_);
lean_dec(v_centenialCycles_495_);
v___y_481_ = v_remDays_494_;
v___y_482_ = v___y_492_;
v___y_483_ = v_quadracentennialCycles_493_;
v_centenialCycles_484_ = v_centenialCycles_497_;
goto v___jp_480_;
}
}
v___jp_498_:
{
lean_object* v_quadracentennialCycles_501_; lean_object* v_remDays_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_quadracentennialCycles_501_ = lean_int_ediv(v_snd_500_, v_daysPer400Y_391_);
v_remDays_502_ = lean_int_emod(v_snd_500_, v_daysPer400Y_391_);
lean_dec(v_snd_500_);
v___x_503_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_504_ = lean_int_dec_lt(v_remDays_502_, v___x_503_);
if (v___x_504_ == 0)
{
v___y_492_ = v_fst_499_;
v_quadracentennialCycles_493_ = v_quadracentennialCycles_501_;
v_remDays_494_ = v_remDays_502_;
goto v___jp_491_;
}
else
{
lean_object* v_remDays_505_; lean_object* v_quadracentennialCycles_506_; 
v_remDays_505_ = lean_int_add(v_remDays_502_, v_daysPer400Y_391_);
lean_dec(v_remDays_502_);
v_quadracentennialCycles_506_ = lean_int_sub(v_quadracentennialCycles_501_, v___x_412_);
lean_dec(v_quadracentennialCycles_501_);
v___y_492_ = v_fst_499_;
v_quadracentennialCycles_493_ = v_quadracentennialCycles_506_;
v_remDays_494_ = v_remDays_505_;
goto v___jp_491_;
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v_boundedDaysSinceEpoch_510_; lean_object* v_rawDays_511_; lean_object* v_h_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_509_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v_boundedDaysSinceEpoch_510_ = lean_int_div(v_snd_508_, v___x_509_);
v_rawDays_511_ = lean_int_sub(v_boundedDaysSinceEpoch_510_, v_leapYearEpoch_388_);
lean_dec(v_boundedDaysSinceEpoch_510_);
v_h_512_ = lean_int_mod(v_snd_508_, v___x_509_);
lean_dec(v_snd_508_);
v___x_513_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__31, &l_Std_Time_PlainDateTime_ofWallTime___closed__31_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31);
v___x_514_ = lean_int_dec_le(v_h_512_, v___x_513_);
if (v___x_514_ == 0)
{
v_fst_499_ = v_h_512_;
v_snd_500_ = v_rawDays_511_;
goto v___jp_498_;
}
else
{
lean_object* v___x_515_; lean_object* v_rawDays_516_; 
v___x_515_ = lean_int_add(v_h_512_, v___x_509_);
lean_dec(v_h_512_);
v_rawDays_516_ = lean_int_sub(v_rawDays_511_, v___x_412_);
lean_dec(v_rawDays_511_);
v_fst_499_ = v___x_515_;
v_snd_500_ = v_rawDays_516_;
goto v___jp_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(lean_object* v_as_523_, lean_object* v_as_x27_524_, lean_object* v_b_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_524_, v_b_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(lean_object* v_as_528_, lean_object* v_as_x27_529_, lean_object* v_b_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(v_as_528_, v_as_x27_529_, v_b_530_, v_a_531_);
lean_dec(v_as_x27_529_);
lean_dec(v_as_528_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object* v_pdt_533_){
_start:
{
lean_object* v_date_534_; lean_object* v___x_535_; 
v_date_534_ = lean_ctor_get(v_pdt_533_, 0);
lean_inc_ref(v_date_534_);
lean_dec_ref(v_pdt_533_);
v___x_535_ = l_Std_Time_PlainDate_toEpochDay(v_date_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object* v_days_536_, lean_object* v_time_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = l_Std_Time_PlainDate_ofEpochDay(v_days_536_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_time_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object* v_days_540_, lean_object* v_time_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_540_, v_time_541_);
lean_dec(v_days_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_543_, uint8_t v_desiredWeekday_544_){
_start:
{
lean_object* v_date_545_; lean_object* v_time_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_date_545_ = lean_ctor_get(v_dt_543_, 0);
v_time_546_ = lean_ctor_get(v_dt_543_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_dt_543_);
if (v_isSharedCheck_554_ == 0)
{
v___x_548_ = v_dt_543_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_time_546_);
lean_inc(v_date_545_);
lean_dec(v_dt_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = l_Std_Time_PlainDate_withWeekday(v_date_545_, v_desiredWeekday_544_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_time_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_555_, lean_object* v_desiredWeekday_556_){
_start:
{
uint8_t v_desiredWeekday_boxed_557_; lean_object* v_res_558_; 
v_desiredWeekday_boxed_557_ = lean_unbox(v_desiredWeekday_556_);
v_res_558_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_555_, v_desiredWeekday_boxed_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_559_, lean_object* v_days_560_){
_start:
{
lean_object* v_date_561_; lean_object* v_time_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_599_; 
v_date_561_ = lean_ctor_get(v_dt_559_, 0);
v_time_562_ = lean_ctor_get(v_dt_559_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_dt_559_);
if (v_isSharedCheck_599_ == 0)
{
v___x_564_ = v_dt_559_;
v_isShared_565_ = v_isSharedCheck_599_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_time_562_);
lean_inc(v_date_561_);
lean_dec(v_dt_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_599_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_year_566_; lean_object* v_month_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_597_; 
v_year_566_ = lean_ctor_get(v_date_561_, 0);
v_month_567_ = lean_ctor_get(v_date_561_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_date_561_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_date_561_, 2);
lean_dec(v_unused_598_);
v___x_569_ = v_date_561_;
v_isShared_570_ = v_isSharedCheck_597_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_month_567_);
lean_inc(v_year_566_);
lean_dec(v_date_561_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_597_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___y_572_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_587_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_588_ = lean_int_mod(v_year_566_, v___x_587_);
v___x_589_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_590_ = lean_int_dec_eq(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
if (v___x_590_ == 0)
{
v___y_572_ = v___x_590_;
goto v___jp_571_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_592_ = lean_int_mod(v_year_566_, v___x_591_);
v___x_593_ = lean_int_dec_eq(v___x_592_, v___x_589_);
lean_dec(v___x_592_);
if (v___x_593_ == 0)
{
v___y_572_ = v___x_590_;
goto v___jp_571_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_595_ = lean_int_mod(v_year_566_, v___x_594_);
v___x_596_ = lean_int_dec_eq(v___x_595_, v___x_589_);
lean_dec(v___x_595_);
v___y_572_ = v___x_596_;
goto v___jp_571_;
}
}
v___jp_571_:
{
lean_object* v_max_573_; uint8_t v___x_574_; 
v_max_573_ = l_Std_Time_Month_Ordinal_days(v___y_572_, v_month_567_);
v___x_574_ = lean_int_dec_lt(v_max_573_, v_days_560_);
if (v___x_574_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v_max_573_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v_days_560_);
v___x_576_ = v___x_569_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_year_566_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_month_567_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_days_560_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_576_);
v___x_578_ = v___x_564_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_time_562_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v___x_582_; 
lean_dec(v_days_560_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v_max_573_);
v___x_582_ = v___x_569_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_year_566_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_month_567_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_max_573_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_582_);
v___x_584_ = v___x_564_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_time_562_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_600_, lean_object* v_days_601_){
_start:
{
lean_object* v_date_602_; lean_object* v_time_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_613_; 
v_date_602_ = lean_ctor_get(v_dt_600_, 0);
v_time_603_ = lean_ctor_get(v_dt_600_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_dt_600_);
if (v_isSharedCheck_613_ == 0)
{
v___x_605_ = v_dt_600_;
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_time_603_);
lean_inc(v_date_602_);
lean_dec(v_dt_600_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_year_607_; lean_object* v_month_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v_year_607_ = lean_ctor_get(v_date_602_, 0);
lean_inc(v_year_607_);
v_month_608_ = lean_ctor_get(v_date_602_, 1);
lean_inc(v_month_608_);
lean_dec_ref(v_date_602_);
v___x_609_ = l_Std_Time_PlainDate_rollOver(v_year_607_, v_month_608_, v_days_601_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_time_603_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_614_, lean_object* v_days_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_614_, v_days_615_);
lean_dec(v_days_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_617_, lean_object* v_month_618_){
_start:
{
lean_object* v_date_619_; lean_object* v_time_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_657_; 
v_date_619_ = lean_ctor_get(v_dt_617_, 0);
v_time_620_ = lean_ctor_get(v_dt_617_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_dt_617_);
if (v_isSharedCheck_657_ == 0)
{
v___x_622_ = v_dt_617_;
v_isShared_623_ = v_isSharedCheck_657_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_time_620_);
lean_inc(v_date_619_);
lean_dec(v_dt_617_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_657_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_year_624_; lean_object* v_day_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_655_; 
v_year_624_ = lean_ctor_get(v_date_619_, 0);
v_day_625_ = lean_ctor_get(v_date_619_, 2);
v_isSharedCheck_655_ = !lean_is_exclusive(v_date_619_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_date_619_, 1);
lean_dec(v_unused_656_);
v___x_627_ = v_date_619_;
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_day_625_);
lean_inc(v_year_624_);
lean_dec(v_date_619_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
uint8_t v___y_630_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_645_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_646_ = lean_int_mod(v_year_624_, v___x_645_);
v___x_647_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_648_ = lean_int_dec_eq(v___x_646_, v___x_647_);
lean_dec(v___x_646_);
if (v___x_648_ == 0)
{
v___y_630_ = v___x_648_;
goto v___jp_629_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_650_ = lean_int_mod(v_year_624_, v___x_649_);
v___x_651_ = lean_int_dec_eq(v___x_650_, v___x_647_);
lean_dec(v___x_650_);
if (v___x_651_ == 0)
{
v___y_630_ = v___x_648_;
goto v___jp_629_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_653_ = lean_int_mod(v_year_624_, v___x_652_);
v___x_654_ = lean_int_dec_eq(v___x_653_, v___x_647_);
lean_dec(v___x_653_);
v___y_630_ = v___x_654_;
goto v___jp_629_;
}
}
v___jp_629_:
{
lean_object* v_max_631_; uint8_t v___x_632_; 
v_max_631_ = l_Std_Time_Month_Ordinal_days(v___y_630_, v_month_618_);
v___x_632_ = lean_int_dec_lt(v_max_631_, v_day_625_);
if (v___x_632_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_max_631_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_month_618_);
v___x_634_ = v___x_627_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_year_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_month_618_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_day_625_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_634_);
v___x_636_ = v___x_622_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_time_620_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_day_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 2, v_max_631_);
lean_ctor_set(v___x_627_, 1, v_month_618_);
v___x_640_ = v___x_627_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_year_624_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_month_618_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_max_631_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_640_);
v___x_642_ = v___x_622_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_time_620_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_658_, lean_object* v_month_659_){
_start:
{
lean_object* v_date_660_; lean_object* v_time_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_671_; 
v_date_660_ = lean_ctor_get(v_dt_658_, 0);
v_time_661_ = lean_ctor_get(v_dt_658_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_dt_658_);
if (v_isSharedCheck_671_ == 0)
{
v___x_663_ = v_dt_658_;
v_isShared_664_ = v_isSharedCheck_671_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_time_661_);
lean_inc(v_date_660_);
lean_dec(v_dt_658_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_671_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_year_665_; lean_object* v_day_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v_year_665_ = lean_ctor_get(v_date_660_, 0);
lean_inc(v_year_665_);
v_day_666_ = lean_ctor_get(v_date_660_, 2);
lean_inc(v_day_666_);
lean_dec_ref(v_date_660_);
v___x_667_ = l_Std_Time_PlainDate_rollOver(v_year_665_, v_month_659_, v_day_666_);
lean_dec(v_day_666_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_667_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_time_661_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_672_, lean_object* v_year_673_){
_start:
{
lean_object* v_date_674_; lean_object* v_time_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_712_; 
v_date_674_ = lean_ctor_get(v_dt_672_, 0);
v_time_675_ = lean_ctor_get(v_dt_672_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_dt_672_);
if (v_isSharedCheck_712_ == 0)
{
v___x_677_ = v_dt_672_;
v_isShared_678_ = v_isSharedCheck_712_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_time_675_);
lean_inc(v_date_674_);
lean_dec(v_dt_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_712_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_month_679_; lean_object* v_day_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_710_; 
v_month_679_ = lean_ctor_get(v_date_674_, 1);
v_day_680_ = lean_ctor_get(v_date_674_, 2);
v_isSharedCheck_710_ = !lean_is_exclusive(v_date_674_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_date_674_, 0);
lean_dec(v_unused_711_);
v___x_682_ = v_date_674_;
v_isShared_683_ = v_isSharedCheck_710_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_day_680_);
lean_inc(v_month_679_);
lean_dec(v_date_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_710_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___y_685_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_700_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_701_ = lean_int_mod(v_year_673_, v___x_700_);
v___x_702_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_703_ = lean_int_dec_eq(v___x_701_, v___x_702_);
lean_dec(v___x_701_);
if (v___x_703_ == 0)
{
v___y_685_ = v___x_703_;
goto v___jp_684_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_705_ = lean_int_mod(v_year_673_, v___x_704_);
v___x_706_ = lean_int_dec_eq(v___x_705_, v___x_702_);
lean_dec(v___x_705_);
if (v___x_706_ == 0)
{
v___y_685_ = v___x_703_;
goto v___jp_684_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_708_ = lean_int_mod(v_year_673_, v___x_707_);
v___x_709_ = lean_int_dec_eq(v___x_708_, v___x_702_);
lean_dec(v___x_708_);
v___y_685_ = v___x_709_;
goto v___jp_684_;
}
}
v___jp_684_:
{
lean_object* v_max_686_; uint8_t v___x_687_; 
v_max_686_ = l_Std_Time_Month_Ordinal_days(v___y_685_, v_month_679_);
v___x_687_ = lean_int_dec_lt(v_max_686_, v_day_680_);
if (v___x_687_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v_max_686_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_year_673_);
v___x_689_ = v___x_682_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_year_673_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_month_679_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_day_680_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_689_);
v___x_691_ = v___x_677_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_time_675_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v_day_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 2, v_max_686_);
lean_ctor_set(v___x_682_, 0, v_year_673_);
v___x_695_ = v___x_682_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_year_673_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_month_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_max_686_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_695_);
v___x_697_ = v___x_677_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_time_675_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_713_, lean_object* v_year_714_){
_start:
{
lean_object* v_date_715_; lean_object* v_time_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_726_; 
v_date_715_ = lean_ctor_get(v_dt_713_, 0);
v_time_716_ = lean_ctor_get(v_dt_713_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_dt_713_);
if (v_isSharedCheck_726_ == 0)
{
v___x_718_ = v_dt_713_;
v_isShared_719_ = v_isSharedCheck_726_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_time_716_);
lean_inc(v_date_715_);
lean_dec(v_dt_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_726_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_month_720_; lean_object* v_day_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v_month_720_ = lean_ctor_get(v_date_715_, 1);
lean_inc(v_month_720_);
v_day_721_ = lean_ctor_get(v_date_715_, 2);
lean_inc(v_day_721_);
lean_dec_ref(v_date_715_);
v___x_722_ = l_Std_Time_PlainDate_rollOver(v_year_714_, v_month_720_, v_day_721_);
lean_dec(v_day_721_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_722_);
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_time_716_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_727_, lean_object* v_hour_728_){
_start:
{
lean_object* v_time_729_; lean_object* v_date_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_748_; 
v_time_729_ = lean_ctor_get(v_dt_727_, 1);
v_date_730_ = lean_ctor_get(v_dt_727_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_dt_727_);
if (v_isSharedCheck_748_ == 0)
{
v___x_732_ = v_dt_727_;
v_isShared_733_ = v_isSharedCheck_748_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_time_729_);
lean_inc(v_date_730_);
lean_dec(v_dt_727_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_748_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_minute_734_; lean_object* v_second_735_; lean_object* v_nanosecond_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_746_; 
v_minute_734_ = lean_ctor_get(v_time_729_, 1);
v_second_735_ = lean_ctor_get(v_time_729_, 2);
v_nanosecond_736_ = lean_ctor_get(v_time_729_, 3);
v_isSharedCheck_746_ = !lean_is_exclusive(v_time_729_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_time_729_, 0);
lean_dec(v_unused_747_);
v___x_738_ = v_time_729_;
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_nanosecond_736_);
lean_inc(v_second_735_);
lean_inc(v_minute_734_);
lean_dec(v_time_729_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_hour_728_);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_hour_728_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_minute_734_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_second_735_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_nanosecond_736_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_741_);
v___x_743_ = v___x_732_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_date_730_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_741_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_749_, lean_object* v_minute_750_){
_start:
{
lean_object* v_time_751_; lean_object* v_date_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_770_; 
v_time_751_ = lean_ctor_get(v_dt_749_, 1);
v_date_752_ = lean_ctor_get(v_dt_749_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_dt_749_);
if (v_isSharedCheck_770_ == 0)
{
v___x_754_ = v_dt_749_;
v_isShared_755_ = v_isSharedCheck_770_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_time_751_);
lean_inc(v_date_752_);
lean_dec(v_dt_749_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_770_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_hour_756_; lean_object* v_second_757_; lean_object* v_nanosecond_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
v_hour_756_ = lean_ctor_get(v_time_751_, 0);
v_second_757_ = lean_ctor_get(v_time_751_, 2);
v_nanosecond_758_ = lean_ctor_get(v_time_751_, 3);
v_isSharedCheck_768_ = !lean_is_exclusive(v_time_751_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_time_751_, 1);
lean_dec(v_unused_769_);
v___x_760_ = v_time_751_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_nanosecond_758_);
lean_inc(v_second_757_);
lean_inc(v_hour_756_);
lean_dec(v_time_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_minute_750_);
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_hour_756_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_minute_750_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_second_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_nanosecond_758_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_763_);
v___x_765_ = v___x_754_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_date_752_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_771_, lean_object* v_second_772_){
_start:
{
lean_object* v_time_773_; lean_object* v_date_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_792_; 
v_time_773_ = lean_ctor_get(v_dt_771_, 1);
v_date_774_ = lean_ctor_get(v_dt_771_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_dt_771_);
if (v_isSharedCheck_792_ == 0)
{
v___x_776_ = v_dt_771_;
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_time_773_);
lean_inc(v_date_774_);
lean_dec(v_dt_771_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_hour_778_; lean_object* v_minute_779_; lean_object* v_nanosecond_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_790_; 
v_hour_778_ = lean_ctor_get(v_time_773_, 0);
v_minute_779_ = lean_ctor_get(v_time_773_, 1);
v_nanosecond_780_ = lean_ctor_get(v_time_773_, 3);
v_isSharedCheck_790_ = !lean_is_exclusive(v_time_773_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_time_773_, 2);
lean_dec(v_unused_791_);
v___x_782_ = v_time_773_;
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_nanosecond_780_);
lean_inc(v_minute_779_);
lean_inc(v_hour_778_);
lean_dec(v_time_773_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 2, v_second_772_);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_hour_778_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_minute_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_second_772_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_nanosecond_780_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_785_);
v___x_787_ = v___x_776_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_date_774_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(1000u);
v___x_794_ = lean_nat_to_int(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(1000000u);
v___x_796_ = lean_nat_to_int(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_797_, lean_object* v_millis_798_){
_start:
{
lean_object* v_time_799_; lean_object* v_date_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_823_; 
v_time_799_ = lean_ctor_get(v_dt_797_, 1);
v_date_800_ = lean_ctor_get(v_dt_797_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_dt_797_);
if (v_isSharedCheck_823_ == 0)
{
v___x_802_ = v_dt_797_;
v_isShared_803_ = v_isSharedCheck_823_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_time_799_);
lean_inc(v_date_800_);
lean_dec(v_dt_797_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_823_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_hour_804_; lean_object* v_minute_805_; lean_object* v_second_806_; lean_object* v_nanosecond_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_822_; 
v_hour_804_ = lean_ctor_get(v_time_799_, 0);
v_minute_805_ = lean_ctor_get(v_time_799_, 1);
v_second_806_ = lean_ctor_get(v_time_799_, 2);
v_nanosecond_807_ = lean_ctor_get(v_time_799_, 3);
v_isSharedCheck_822_ = !lean_is_exclusive(v_time_799_);
if (v_isSharedCheck_822_ == 0)
{
v___x_809_ = v_time_799_;
v_isShared_810_ = v_isSharedCheck_822_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_nanosecond_807_);
lean_inc(v_second_806_);
lean_inc(v_minute_805_);
lean_inc(v_hour_804_);
lean_dec(v_time_799_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_822_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_811_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_812_ = lean_int_emod(v_nanosecond_807_, v___x_811_);
lean_dec(v_nanosecond_807_);
v___x_813_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_814_ = lean_int_mul(v_millis_798_, v___x_813_);
v___x_815_ = lean_int_add(v___x_814_, v___x_812_);
lean_dec(v___x_812_);
lean_dec(v___x_814_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 3, v___x_815_);
v___x_817_ = v___x_809_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_hour_804_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_minute_805_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_second_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___x_815_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_817_);
v___x_819_ = v___x_802_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_date_800_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_824_, lean_object* v_millis_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_824_, v_millis_825_);
lean_dec(v_millis_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_827_, lean_object* v_nano_828_){
_start:
{
lean_object* v_time_829_; lean_object* v_date_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_848_; 
v_time_829_ = lean_ctor_get(v_dt_827_, 1);
v_date_830_ = lean_ctor_get(v_dt_827_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_dt_827_);
if (v_isSharedCheck_848_ == 0)
{
v___x_832_ = v_dt_827_;
v_isShared_833_ = v_isSharedCheck_848_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_time_829_);
lean_inc(v_date_830_);
lean_dec(v_dt_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_848_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_hour_834_; lean_object* v_minute_835_; lean_object* v_second_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_846_; 
v_hour_834_ = lean_ctor_get(v_time_829_, 0);
v_minute_835_ = lean_ctor_get(v_time_829_, 1);
v_second_836_ = lean_ctor_get(v_time_829_, 2);
v_isSharedCheck_846_ = !lean_is_exclusive(v_time_829_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_time_829_, 3);
lean_dec(v_unused_847_);
v___x_838_ = v_time_829_;
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_second_836_);
lean_inc(v_minute_835_);
lean_inc(v_hour_834_);
lean_dec(v_time_829_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 3, v_nano_828_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_hour_834_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_minute_835_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_second_836_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_nano_828_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_841_);
v___x_843_ = v___x_832_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_date_830_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_849_, lean_object* v_days_850_){
_start:
{
lean_object* v_date_851_; lean_object* v_time_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_date_851_ = lean_ctor_get(v_dt_849_, 0);
v_time_852_ = lean_ctor_get(v_dt_849_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_dt_849_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v_dt_849_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_time_852_);
lean_inc(v_date_851_);
lean_dec(v_dt_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_dateDays_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v_dateDays_856_ = l_Std_Time_PlainDate_toEpochDay(v_date_851_);
v___x_857_ = lean_int_add(v_dateDays_856_, v_days_850_);
lean_dec(v_dateDays_856_);
v___x_858_ = l_Std_Time_PlainDate_ofEpochDay(v___x_857_);
lean_dec(v___x_857_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_858_);
v___x_860_ = v___x_854_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_time_852_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_863_, lean_object* v_days_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_Time_PlainDateTime_addDays(v_dt_863_, v_days_864_);
lean_dec(v_days_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_866_, lean_object* v_days_867_){
_start:
{
lean_object* v_date_868_; lean_object* v_time_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_880_; 
v_date_868_ = lean_ctor_get(v_dt_866_, 0);
v_time_869_ = lean_ctor_get(v_dt_866_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_dt_866_);
if (v_isSharedCheck_880_ == 0)
{
v___x_871_ = v_dt_866_;
v_isShared_872_ = v_isSharedCheck_880_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_time_869_);
lean_inc(v_date_868_);
lean_dec(v_dt_866_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_880_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v_dateDays_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_873_ = lean_int_neg(v_days_867_);
v_dateDays_874_ = l_Std_Time_PlainDate_toEpochDay(v_date_868_);
v___x_875_ = lean_int_add(v_dateDays_874_, v___x_873_);
lean_dec(v___x_873_);
lean_dec(v_dateDays_874_);
v___x_876_ = l_Std_Time_PlainDate_ofEpochDay(v___x_875_);
lean_dec(v___x_875_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_876_);
v___x_878_ = v___x_871_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_time_869_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_881_, lean_object* v_days_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_Time_PlainDateTime_subDays(v_dt_881_, v_days_882_);
lean_dec(v_days_882_);
return v_res_883_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(7u);
v___x_885_ = lean_nat_to_int(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_886_, lean_object* v_weeks_887_){
_start:
{
lean_object* v_date_888_; lean_object* v_time_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_date_888_ = lean_ctor_get(v_dt_886_, 0);
v_time_889_ = lean_ctor_get(v_dt_886_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_dt_886_);
if (v_isSharedCheck_901_ == 0)
{
v___x_891_ = v_dt_886_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_time_889_);
lean_inc(v_date_888_);
lean_dec(v_dt_886_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_dateDays_893_; lean_object* v___x_894_; lean_object* v_daysToAdd_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v_dateDays_893_ = l_Std_Time_PlainDate_toEpochDay(v_date_888_);
v___x_894_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_895_ = lean_int_mul(v_weeks_887_, v___x_894_);
v___x_896_ = lean_int_add(v_dateDays_893_, v_daysToAdd_895_);
lean_dec(v_daysToAdd_895_);
lean_dec(v_dateDays_893_);
v___x_897_ = l_Std_Time_PlainDate_ofEpochDay(v___x_896_);
lean_dec(v___x_896_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_897_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_time_889_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_902_, lean_object* v_weeks_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_902_, v_weeks_903_);
lean_dec(v_weeks_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_905_, lean_object* v_weeks_906_){
_start:
{
lean_object* v_date_907_; lean_object* v_time_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_921_; 
v_date_907_ = lean_ctor_get(v_dt_905_, 0);
v_time_908_ = lean_ctor_get(v_dt_905_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_dt_905_);
if (v_isSharedCheck_921_ == 0)
{
v___x_910_ = v_dt_905_;
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_time_908_);
lean_inc(v_date_907_);
lean_dec(v_dt_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v_dateDays_913_; lean_object* v___x_914_; lean_object* v_daysToAdd_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_912_ = lean_int_neg(v_weeks_906_);
v_dateDays_913_ = l_Std_Time_PlainDate_toEpochDay(v_date_907_);
v___x_914_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_915_ = lean_int_mul(v___x_912_, v___x_914_);
lean_dec(v___x_912_);
v___x_916_ = lean_int_add(v_dateDays_913_, v_daysToAdd_915_);
lean_dec(v_daysToAdd_915_);
lean_dec(v_dateDays_913_);
v___x_917_ = l_Std_Time_PlainDate_ofEpochDay(v___x_916_);
lean_dec(v___x_916_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_917_);
v___x_919_ = v___x_910_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_time_908_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_922_, lean_object* v_weeks_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_922_, v_weeks_923_);
lean_dec(v_weeks_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_925_, lean_object* v_months_926_){
_start:
{
lean_object* v_date_927_; lean_object* v_time_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
v_date_927_ = lean_ctor_get(v_dt_925_, 0);
v_time_928_ = lean_ctor_get(v_dt_925_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_dt_925_);
if (v_isSharedCheck_936_ == 0)
{
v___x_930_ = v_dt_925_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_time_928_);
lean_inc(v_date_927_);
lean_dec(v_dt_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_Std_Time_PlainDate_addMonthsClip(v_date_927_, v_months_926_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_time_928_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_937_, lean_object* v_months_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_937_, v_months_938_);
lean_dec(v_months_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_940_, lean_object* v_months_941_){
_start:
{
lean_object* v_date_942_; lean_object* v_time_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_952_; 
v_date_942_ = lean_ctor_get(v_dt_940_, 0);
v_time_943_ = lean_ctor_get(v_dt_940_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_dt_940_);
if (v_isSharedCheck_952_ == 0)
{
v___x_945_ = v_dt_940_;
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_time_943_);
lean_inc(v_date_942_);
lean_dec(v_dt_940_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_947_ = lean_int_neg(v_months_941_);
v___x_948_ = l_Std_Time_PlainDate_addMonthsClip(v_date_942_, v___x_947_);
lean_dec(v___x_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_948_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_time_943_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_953_, lean_object* v_months_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_953_, v_months_954_);
lean_dec(v_months_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_956_, lean_object* v_months_957_){
_start:
{
lean_object* v_date_958_; lean_object* v_time_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
v_date_958_ = lean_ctor_get(v_dt_956_, 0);
v_time_959_ = lean_ctor_get(v_dt_956_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_dt_956_);
if (v_isSharedCheck_967_ == 0)
{
v___x_961_ = v_dt_956_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_time_959_);
lean_inc(v_date_958_);
lean_dec(v_dt_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_958_, v_months_957_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_time_959_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_968_, lean_object* v_months_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_968_, v_months_969_);
lean_dec(v_months_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_971_, lean_object* v_months_972_){
_start:
{
lean_object* v_date_973_; lean_object* v_time_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_983_; 
v_date_973_ = lean_ctor_get(v_dt_971_, 0);
v_time_974_ = lean_ctor_get(v_dt_971_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_dt_971_);
if (v_isSharedCheck_983_ == 0)
{
v___x_976_ = v_dt_971_;
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_time_974_);
lean_inc(v_date_973_);
lean_dec(v_dt_971_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_978_ = lean_int_neg(v_months_972_);
v___x_979_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_973_, v___x_978_);
lean_dec(v___x_978_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_981_ = v___x_976_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_time_974_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_984_, lean_object* v_months_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_984_, v_months_985_);
lean_dec(v_months_985_);
return v_res_986_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_unsigned_to_nat(12u);
v___x_988_ = lean_nat_to_int(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_989_, lean_object* v_years_990_){
_start:
{
lean_object* v_date_991_; lean_object* v_time_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1002_; 
v_date_991_ = lean_ctor_get(v_dt_989_, 0);
v_time_992_ = lean_ctor_get(v_dt_989_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_dt_989_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_994_ = v_dt_989_;
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_time_992_);
lean_inc(v_date_991_);
lean_dec(v_dt_989_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_996_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_997_ = lean_int_mul(v_years_990_, v___x_996_);
v___x_998_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_991_, v___x_997_);
lean_dec(v___x_997_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_998_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_time_992_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_1003_, lean_object* v_years_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_1003_, v_years_1004_);
lean_dec(v_years_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_1006_, lean_object* v_years_1007_){
_start:
{
lean_object* v_date_1008_; lean_object* v_time_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1019_; 
v_date_1008_ = lean_ctor_get(v_dt_1006_, 0);
v_time_1009_ = lean_ctor_get(v_dt_1006_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_dt_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1011_ = v_dt_1006_;
v_isShared_1012_ = v_isSharedCheck_1019_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_time_1009_);
lean_inc(v_date_1008_);
lean_dec(v_dt_1006_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1019_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1013_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1014_ = lean_int_mul(v_years_1007_, v___x_1013_);
v___x_1015_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1008_, v___x_1014_);
lean_dec(v___x_1014_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1015_);
v___x_1017_ = v___x_1011_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_time_1009_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_1020_, lean_object* v_years_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_1020_, v_years_1021_);
lean_dec(v_years_1021_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_1023_, lean_object* v_years_1024_){
_start:
{
lean_object* v_date_1025_; lean_object* v_time_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1037_; 
v_date_1025_ = lean_ctor_get(v_dt_1023_, 0);
v_time_1026_ = lean_ctor_get(v_dt_1023_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_dt_1023_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1028_ = v_dt_1023_;
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_time_1026_);
lean_inc(v_date_1025_);
lean_dec(v_dt_1023_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1030_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1031_ = lean_int_mul(v_years_1024_, v___x_1030_);
v___x_1032_ = lean_int_neg(v___x_1031_);
lean_dec(v___x_1031_);
v___x_1033_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1025_, v___x_1032_);
lean_dec(v___x_1032_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1033_);
v___x_1035_ = v___x_1028_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_time_1026_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_1038_, lean_object* v_years_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_1038_, v_years_1039_);
lean_dec(v_years_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_1041_, lean_object* v_years_1042_){
_start:
{
lean_object* v_date_1043_; lean_object* v_time_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1055_; 
v_date_1043_ = lean_ctor_get(v_dt_1041_, 0);
v_time_1044_ = lean_ctor_get(v_dt_1041_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_dt_1041_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1046_ = v_dt_1041_;
v_isShared_1047_ = v_isSharedCheck_1055_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_time_1044_);
lean_inc(v_date_1043_);
lean_dec(v_dt_1041_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1055_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1048_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1049_ = lean_int_mul(v_years_1042_, v___x_1048_);
v___x_1050_ = lean_int_neg(v___x_1049_);
lean_dec(v___x_1049_);
v___x_1051_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1043_, v___x_1050_);
lean_dec(v___x_1050_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1051_);
v___x_1053_ = v___x_1046_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_time_1044_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_1056_, lean_object* v_years_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_1056_, v_years_1057_);
lean_dec(v_years_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_1059_, lean_object* v_nanos_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v_second_1062_; lean_object* v_nano_1063_; lean_object* v___x_1064_; lean_object* v_second_1065_; lean_object* v_nano_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_nanos_1069_; lean_object* v___x_1070_; lean_object* v_nanos_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1061_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1059_);
v_second_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_second_1062_);
v_nano_1063_ = lean_ctor_get(v___x_1061_, 1);
lean_inc(v_nano_1063_);
lean_dec_ref(v___x_1061_);
v___x_1064_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1060_);
v_second_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_second_1065_);
v_nano_1066_ = lean_ctor_get(v___x_1064_, 1);
lean_inc(v_nano_1066_);
lean_dec_ref(v___x_1064_);
v___x_1067_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1068_ = lean_int_mul(v_second_1062_, v___x_1067_);
lean_dec(v_second_1062_);
v_nanos_1069_ = lean_int_add(v___x_1068_, v_nano_1063_);
lean_dec(v_nano_1063_);
lean_dec(v___x_1068_);
v___x_1070_ = lean_int_mul(v_second_1065_, v___x_1067_);
lean_dec(v_second_1065_);
v_nanos_1071_ = lean_int_add(v___x_1070_, v_nano_1066_);
lean_dec(v_nano_1066_);
lean_dec(v___x_1070_);
v___x_1072_ = lean_int_add(v_nanos_1069_, v_nanos_1071_);
lean_dec(v_nanos_1071_);
lean_dec(v_nanos_1069_);
v___x_1073_ = l_Std_Time_Duration_ofNanoseconds(v___x_1072_);
lean_dec(v___x_1072_);
v___x_1074_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_1075_, lean_object* v_nanos_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_1075_, v_nanos_1076_);
lean_dec(v_nanos_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_1078_, lean_object* v_nanos_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v_second_1081_; lean_object* v_nano_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_second_1085_; lean_object* v_nano_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_nanos_1089_; lean_object* v___x_1090_; lean_object* v_nanos_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1080_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1078_);
v_second_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_second_1081_);
v_nano_1082_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_nano_1082_);
lean_dec_ref(v___x_1080_);
v___x_1083_ = lean_int_neg(v_nanos_1079_);
v___x_1084_ = l_Std_Time_Duration_ofNanoseconds(v___x_1083_);
lean_dec(v___x_1083_);
v_second_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_second_1085_);
v_nano_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_nano_1086_);
lean_dec_ref(v___x_1084_);
v___x_1087_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1088_ = lean_int_mul(v_second_1081_, v___x_1087_);
lean_dec(v_second_1081_);
v_nanos_1089_ = lean_int_add(v___x_1088_, v_nano_1082_);
lean_dec(v_nano_1082_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_1095_, lean_object* v_nanos_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_1095_, v_nanos_1096_);
lean_dec(v_nanos_1096_);
return v_res_1097_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_cstr_to_nat("3600000000000");
v___x_1099_ = lean_nat_to_int(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_1100_, lean_object* v_hours_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v_second_1103_; lean_object* v_nano_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_second_1108_; lean_object* v_nano_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_nanos_1112_; lean_object* v___x_1113_; lean_object* v_nanos_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1102_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1100_);
v_second_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_second_1103_);
v_nano_1104_ = lean_ctor_get(v___x_1102_, 1);
lean_inc(v_nano_1104_);
lean_dec_ref(v___x_1102_);
v___x_1105_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1106_ = lean_int_mul(v_hours_1101_, v___x_1105_);
v___x_1107_ = l_Std_Time_Duration_ofNanoseconds(v___x_1106_);
lean_dec(v___x_1106_);
v_second_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_second_1108_);
v_nano_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_nano_1109_);
lean_dec_ref(v___x_1107_);
v___x_1110_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1111_ = lean_int_mul(v_second_1103_, v___x_1110_);
lean_dec(v_second_1103_);
v_nanos_1112_ = lean_int_add(v___x_1111_, v_nano_1104_);
lean_dec(v_nano_1104_);
lean_dec(v___x_1111_);
v___x_1113_ = lean_int_mul(v_second_1108_, v___x_1110_);
lean_dec(v_second_1108_);
v_nanos_1114_ = lean_int_add(v___x_1113_, v_nano_1109_);
lean_dec(v_nano_1109_);
lean_dec(v___x_1113_);
v___x_1115_ = lean_int_add(v_nanos_1112_, v_nanos_1114_);
lean_dec(v_nanos_1114_);
lean_dec(v_nanos_1112_);
v___x_1116_ = l_Std_Time_Duration_ofNanoseconds(v___x_1115_);
lean_dec(v___x_1115_);
v___x_1117_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_1118_, lean_object* v_hours_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_Time_PlainDateTime_addHours(v_dt_1118_, v_hours_1119_);
lean_dec(v_hours_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_1121_, lean_object* v_hours_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v_second_1124_; lean_object* v_nano_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_second_1130_; lean_object* v_nano_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_nanos_1134_; lean_object* v___x_1135_; lean_object* v_nanos_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1123_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1121_);
v_second_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_second_1124_);
v_nano_1125_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_nano_1125_);
lean_dec_ref(v___x_1123_);
v___x_1126_ = lean_int_neg(v_hours_1122_);
v___x_1127_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1128_ = lean_int_mul(v___x_1126_, v___x_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = l_Std_Time_Duration_ofNanoseconds(v___x_1128_);
lean_dec(v___x_1128_);
v_second_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_second_1130_);
v_nano_1131_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_nano_1131_);
lean_dec_ref(v___x_1129_);
v___x_1132_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1133_ = lean_int_mul(v_second_1124_, v___x_1132_);
lean_dec(v_second_1124_);
v_nanos_1134_ = lean_int_add(v___x_1133_, v_nano_1125_);
lean_dec(v_nano_1125_);
lean_dec(v___x_1133_);
v___x_1135_ = lean_int_mul(v_second_1130_, v___x_1132_);
lean_dec(v_second_1130_);
v_nanos_1136_ = lean_int_add(v___x_1135_, v_nano_1131_);
lean_dec(v_nano_1131_);
lean_dec(v___x_1135_);
v___x_1137_ = lean_int_add(v_nanos_1134_, v_nanos_1136_);
lean_dec(v_nanos_1136_);
lean_dec(v_nanos_1134_);
v___x_1138_ = l_Std_Time_Duration_ofNanoseconds(v___x_1137_);
lean_dec(v___x_1137_);
v___x_1139_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_1140_, lean_object* v_hours_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_Time_PlainDateTime_subHours(v_dt_1140_, v_hours_1141_);
lean_dec(v_hours_1141_);
return v_res_1142_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_cstr_to_nat("60000000000");
v___x_1144_ = lean_nat_to_int(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_1145_, lean_object* v_minutes_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v_second_1148_; lean_object* v_nano_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_second_1153_; lean_object* v_nano_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_nanos_1157_; lean_object* v___x_1158_; lean_object* v_nanos_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1147_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1145_);
v_second_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_second_1148_);
v_nano_1149_ = lean_ctor_get(v___x_1147_, 1);
lean_inc(v_nano_1149_);
lean_dec_ref(v___x_1147_);
v___x_1150_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1151_ = lean_int_mul(v_minutes_1146_, v___x_1150_);
v___x_1152_ = l_Std_Time_Duration_ofNanoseconds(v___x_1151_);
lean_dec(v___x_1151_);
v_second_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_second_1153_);
v_nano_1154_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_nano_1154_);
lean_dec_ref(v___x_1152_);
v___x_1155_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1156_ = lean_int_mul(v_second_1148_, v___x_1155_);
lean_dec(v_second_1148_);
v_nanos_1157_ = lean_int_add(v___x_1156_, v_nano_1149_);
lean_dec(v_nano_1149_);
lean_dec(v___x_1156_);
v___x_1158_ = lean_int_mul(v_second_1153_, v___x_1155_);
lean_dec(v_second_1153_);
v_nanos_1159_ = lean_int_add(v___x_1158_, v_nano_1154_);
lean_dec(v_nano_1154_);
lean_dec(v___x_1158_);
v___x_1160_ = lean_int_add(v_nanos_1157_, v_nanos_1159_);
lean_dec(v_nanos_1159_);
lean_dec(v_nanos_1157_);
v___x_1161_ = l_Std_Time_Duration_ofNanoseconds(v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_1163_, lean_object* v_minutes_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_1163_, v_minutes_1164_);
lean_dec(v_minutes_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_1166_, lean_object* v_minutes_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v_second_1169_; lean_object* v_nano_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_second_1175_; lean_object* v_nano_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_nanos_1179_; lean_object* v___x_1180_; lean_object* v_nanos_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1168_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1166_);
v_second_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_second_1169_);
v_nano_1170_ = lean_ctor_get(v___x_1168_, 1);
lean_inc(v_nano_1170_);
lean_dec_ref(v___x_1168_);
v___x_1171_ = lean_int_neg(v_minutes_1167_);
v___x_1172_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1173_ = lean_int_mul(v___x_1171_, v___x_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = l_Std_Time_Duration_ofNanoseconds(v___x_1173_);
lean_dec(v___x_1173_);
v_second_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_second_1175_);
v_nano_1176_ = lean_ctor_get(v___x_1174_, 1);
lean_inc(v_nano_1176_);
lean_dec_ref(v___x_1174_);
v___x_1177_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1178_ = lean_int_mul(v_second_1169_, v___x_1177_);
lean_dec(v_second_1169_);
v_nanos_1179_ = lean_int_add(v___x_1178_, v_nano_1170_);
lean_dec(v_nano_1170_);
lean_dec(v___x_1178_);
v___x_1180_ = lean_int_mul(v_second_1175_, v___x_1177_);
lean_dec(v_second_1175_);
v_nanos_1181_ = lean_int_add(v___x_1180_, v_nano_1176_);
lean_dec(v_nano_1176_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_int_add(v_nanos_1179_, v_nanos_1181_);
lean_dec(v_nanos_1181_);
lean_dec(v_nanos_1179_);
v___x_1183_ = l_Std_Time_Duration_ofNanoseconds(v___x_1182_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_1185_, lean_object* v_minutes_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_1185_, v_minutes_1186_);
lean_dec(v_minutes_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_1188_, lean_object* v_seconds_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v_second_1191_; lean_object* v_nano_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_second_1196_; lean_object* v_nano_1197_; lean_object* v___x_1198_; lean_object* v_nanos_1199_; lean_object* v___x_1200_; lean_object* v_nanos_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1190_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1188_);
v_second_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_second_1191_);
v_nano_1192_ = lean_ctor_get(v___x_1190_, 1);
lean_inc(v_nano_1192_);
lean_dec_ref(v___x_1190_);
v___x_1193_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1194_ = lean_int_mul(v_seconds_1189_, v___x_1193_);
v___x_1195_ = l_Std_Time_Duration_ofNanoseconds(v___x_1194_);
lean_dec(v___x_1194_);
v_second_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_second_1196_);
v_nano_1197_ = lean_ctor_get(v___x_1195_, 1);
lean_inc(v_nano_1197_);
lean_dec_ref(v___x_1195_);
v___x_1198_ = lean_int_mul(v_second_1191_, v___x_1193_);
lean_dec(v_second_1191_);
v_nanos_1199_ = lean_int_add(v___x_1198_, v_nano_1192_);
lean_dec(v_nano_1192_);
lean_dec(v___x_1198_);
v___x_1200_ = lean_int_mul(v_second_1196_, v___x_1193_);
lean_dec(v_second_1196_);
v_nanos_1201_ = lean_int_add(v___x_1200_, v_nano_1197_);
lean_dec(v_nano_1197_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_1205_, lean_object* v_seconds_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_1205_, v_seconds_1206_);
lean_dec(v_seconds_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_1208_, lean_object* v_seconds_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v_second_1211_; lean_object* v_nano_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_second_1217_; lean_object* v_nano_1218_; lean_object* v___x_1219_; lean_object* v_nanos_1220_; lean_object* v___x_1221_; lean_object* v_nanos_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1210_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1208_);
v_second_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_second_1211_);
v_nano_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_nano_1212_);
lean_dec_ref(v___x_1210_);
v___x_1213_ = lean_int_neg(v_seconds_1209_);
v___x_1214_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1215_ = lean_int_mul(v___x_1213_, v___x_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = l_Std_Time_Duration_ofNanoseconds(v___x_1215_);
lean_dec(v___x_1215_);
v_second_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_second_1217_);
v_nano_1218_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_nano_1218_);
lean_dec_ref(v___x_1216_);
v___x_1219_ = lean_int_mul(v_second_1211_, v___x_1214_);
lean_dec(v_second_1211_);
v_nanos_1220_ = lean_int_add(v___x_1219_, v_nano_1212_);
lean_dec(v_nano_1212_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_int_mul(v_second_1217_, v___x_1214_);
lean_dec(v_second_1217_);
v_nanos_1222_ = lean_int_add(v___x_1221_, v_nano_1218_);
lean_dec(v_nano_1218_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_int_add(v_nanos_1220_, v_nanos_1222_);
lean_dec(v_nanos_1222_);
lean_dec(v_nanos_1220_);
v___x_1224_ = l_Std_Time_Duration_ofNanoseconds(v___x_1223_);
lean_dec(v___x_1223_);
v___x_1225_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_1226_, lean_object* v_seconds_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_1226_, v_seconds_1227_);
lean_dec(v_seconds_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_1229_, lean_object* v_milliseconds_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v_second_1232_; lean_object* v_nano_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_second_1237_; lean_object* v_nano_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_nanos_1241_; lean_object* v___x_1242_; lean_object* v_nanos_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1231_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1229_);
v_second_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_second_1232_);
v_nano_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_nano_1233_);
lean_dec_ref(v___x_1231_);
v___x_1234_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1235_ = lean_int_mul(v_milliseconds_1230_, v___x_1234_);
v___x_1236_ = l_Std_Time_Duration_ofNanoseconds(v___x_1235_);
lean_dec(v___x_1235_);
v_second_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_second_1237_);
v_nano_1238_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_nano_1238_);
lean_dec_ref(v___x_1236_);
v___x_1239_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1240_ = lean_int_mul(v_second_1232_, v___x_1239_);
lean_dec(v_second_1232_);
v_nanos_1241_ = lean_int_add(v___x_1240_, v_nano_1233_);
lean_dec(v_nano_1233_);
lean_dec(v___x_1240_);
v___x_1242_ = lean_int_mul(v_second_1237_, v___x_1239_);
lean_dec(v_second_1237_);
v_nanos_1243_ = lean_int_add(v___x_1242_, v_nano_1238_);
lean_dec(v_nano_1238_);
lean_dec(v___x_1242_);
v___x_1244_ = lean_int_add(v_nanos_1241_, v_nanos_1243_);
lean_dec(v_nanos_1243_);
lean_dec(v_nanos_1241_);
v___x_1245_ = l_Std_Time_Duration_ofNanoseconds(v___x_1244_);
lean_dec(v___x_1244_);
v___x_1246_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_1247_, lean_object* v_milliseconds_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_1247_, v_milliseconds_1248_);
lean_dec(v_milliseconds_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_1250_, lean_object* v_milliseconds_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v_second_1253_; lean_object* v_nano_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_second_1259_; lean_object* v_nano_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v_nanos_1263_; lean_object* v___x_1264_; lean_object* v_nanos_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1252_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1250_);
v_second_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_second_1253_);
v_nano_1254_ = lean_ctor_get(v___x_1252_, 1);
lean_inc(v_nano_1254_);
lean_dec_ref(v___x_1252_);
v___x_1255_ = lean_int_neg(v_milliseconds_1251_);
v___x_1256_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1257_ = lean_int_mul(v___x_1255_, v___x_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = l_Std_Time_Duration_ofNanoseconds(v___x_1257_);
lean_dec(v___x_1257_);
v_second_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_second_1259_);
v_nano_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_nano_1260_);
lean_dec_ref(v___x_1258_);
v___x_1261_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1262_ = lean_int_mul(v_second_1253_, v___x_1261_);
lean_dec(v_second_1253_);
v_nanos_1263_ = lean_int_add(v___x_1262_, v_nano_1254_);
lean_dec(v_nano_1254_);
lean_dec(v___x_1262_);
v___x_1264_ = lean_int_mul(v_second_1259_, v___x_1261_);
lean_dec(v_second_1259_);
v_nanos_1265_ = lean_int_add(v___x_1264_, v_nano_1260_);
lean_dec(v_nano_1260_);
lean_dec(v___x_1264_);
v___x_1266_ = lean_int_add(v_nanos_1263_, v_nanos_1265_);
lean_dec(v_nanos_1265_);
lean_dec(v_nanos_1263_);
v___x_1267_ = l_Std_Time_Duration_ofNanoseconds(v___x_1266_);
lean_dec(v___x_1266_);
v___x_1268_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1269_, lean_object* v_milliseconds_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1269_, v_milliseconds_1270_);
lean_dec(v_milliseconds_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1272_){
_start:
{
lean_object* v_date_1273_; lean_object* v_year_1274_; 
v_date_1273_ = lean_ctor_get(v_dt_1272_, 0);
v_year_1274_ = lean_ctor_get(v_date_1273_, 0);
lean_inc(v_year_1274_);
return v_year_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Time_PlainDateTime_year(v_dt_1275_);
lean_dec_ref(v_dt_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1277_){
_start:
{
lean_object* v_date_1278_; lean_object* v_month_1279_; 
v_date_1278_ = lean_ctor_get(v_dt_1277_, 0);
v_month_1279_ = lean_ctor_get(v_date_1278_, 1);
lean_inc(v_month_1279_);
return v_month_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_Time_PlainDateTime_month(v_dt_1280_);
lean_dec_ref(v_dt_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1282_){
_start:
{
lean_object* v_date_1283_; lean_object* v_day_1284_; 
v_date_1283_ = lean_ctor_get(v_dt_1282_, 0);
v_day_1284_ = lean_ctor_get(v_date_1283_, 2);
lean_inc(v_day_1284_);
return v_day_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_Time_PlainDateTime_day(v_dt_1285_);
lean_dec_ref(v_dt_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1287_){
_start:
{
lean_object* v_date_1288_; uint8_t v___x_1289_; 
v_date_1288_ = lean_ctor_get(v_dt_1287_, 0);
lean_inc_ref(v_date_1288_);
lean_dec_ref(v_dt_1287_);
v___x_1289_ = l_Std_Time_PlainDate_weekday(v_date_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Std_Time_PlainDateTime_weekday(v_dt_1290_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1293_){
_start:
{
lean_object* v_time_1294_; lean_object* v_hour_1295_; 
v_time_1294_ = lean_ctor_get(v_dt_1293_, 1);
v_hour_1295_ = lean_ctor_get(v_time_1294_, 0);
lean_inc(v_hour_1295_);
return v_hour_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_Time_PlainDateTime_hour(v_dt_1296_);
lean_dec_ref(v_dt_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1298_){
_start:
{
lean_object* v_time_1299_; lean_object* v_minute_1300_; 
v_time_1299_ = lean_ctor_get(v_dt_1298_, 1);
v_minute_1300_ = lean_ctor_get(v_time_1299_, 1);
lean_inc(v_minute_1300_);
return v_minute_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_Time_PlainDateTime_minute(v_dt_1301_);
lean_dec_ref(v_dt_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1303_){
_start:
{
lean_object* v_time_1304_; lean_object* v_nanosecond_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_time_1304_ = lean_ctor_get(v_dt_1303_, 1);
v_nanosecond_1305_ = lean_ctor_get(v_time_1304_, 3);
v___x_1306_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1307_ = lean_int_ediv(v_nanosecond_1305_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1308_);
lean_dec_ref(v_dt_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1310_){
_start:
{
lean_object* v_time_1311_; lean_object* v_second_1312_; 
v_time_1311_ = lean_ctor_get(v_dt_1310_, 1);
v_second_1312_ = lean_ctor_get(v_time_1311_, 2);
lean_inc(v_second_1312_);
return v_second_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_Time_PlainDateTime_second(v_dt_1313_);
lean_dec_ref(v_dt_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1315_){
_start:
{
lean_object* v_time_1316_; lean_object* v_nanosecond_1317_; 
v_time_1316_ = lean_ctor_get(v_dt_1315_, 1);
v_nanosecond_1317_ = lean_ctor_get(v_time_1316_, 3);
lean_inc(v_nanosecond_1317_);
return v_nanosecond_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1318_);
lean_dec_ref(v_dt_1318_);
return v_res_1319_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1320_){
_start:
{
lean_object* v_date_1321_; lean_object* v_year_1322_; uint8_t v___x_1323_; 
v_date_1321_ = lean_ctor_get(v_date_1320_, 0);
v_year_1322_ = lean_ctor_get(v_date_1321_, 0);
v___x_1323_ = l_Std_Time_Year_Offset_era(v_year_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Std_Time_PlainDateTime_era(v_date_1324_);
lean_dec_ref(v_date_1324_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1327_){
_start:
{
lean_object* v_date_1328_; lean_object* v_year_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_date_1328_ = lean_ctor_get(v_date_1327_, 0);
v_year_1329_ = lean_ctor_get(v_date_1328_, 0);
v___x_1330_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1331_ = lean_int_mod(v_year_1329_, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1333_ = lean_int_dec_eq(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
if (v___x_1333_ == 0)
{
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1334_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1335_ = lean_int_mod(v_year_1329_, v___x_1334_);
v___x_1336_ = lean_int_dec_eq(v___x_1335_, v___x_1332_);
lean_dec(v___x_1335_);
if (v___x_1336_ == 0)
{
return v___x_1333_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1338_ = lean_int_mod(v_year_1329_, v___x_1337_);
v___x_1339_ = lean_int_dec_eq(v___x_1338_, v___x_1332_);
lean_dec(v___x_1338_);
return v___x_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object* v_date_1340_){
_start:
{
uint8_t v_res_1341_; lean_object* v_r_1342_; 
v_res_1341_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1340_);
lean_dec_ref(v_date_1340_);
v_r_1342_ = lean_box(v_res_1341_);
return v_r_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1343_, uint8_t v_firstDay_1344_, lean_object* v_minDays_1345_){
_start:
{
lean_object* v_date_1346_; lean_object* v___x_1347_; 
v_date_1346_ = lean_ctor_get(v_date_1343_, 0);
lean_inc_ref(v_date_1346_);
lean_dec_ref(v_date_1343_);
v___x_1347_ = l_Std_Time_PlainDate_weekOfYear(v_date_1346_, v_firstDay_1344_, v_minDays_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear___boxed(lean_object* v_date_1348_, lean_object* v_firstDay_1349_, lean_object* v_minDays_1350_){
_start:
{
uint8_t v_firstDay_boxed_1351_; lean_object* v_res_1352_; 
v_firstDay_boxed_1351_ = lean_unbox(v_firstDay_1349_);
v_res_1352_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_1348_, v_firstDay_boxed_1351_, v_minDays_1350_);
lean_dec(v_minDays_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object* v_date_1353_, uint8_t v_firstDay_1354_, lean_object* v_minDays_1355_){
_start:
{
lean_object* v_date_1356_; lean_object* v___x_1357_; 
v_date_1356_ = lean_ctor_get(v_date_1353_, 0);
lean_inc_ref(v_date_1356_);
lean_dec_ref(v_date_1353_);
v___x_1357_ = l_Std_Time_PlainDate_weekYear(v_date_1356_, v_firstDay_1354_, v_minDays_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object* v_date_1358_, lean_object* v_firstDay_1359_, lean_object* v_minDays_1360_){
_start:
{
uint8_t v_firstDay_boxed_1361_; lean_object* v_res_1362_; 
v_firstDay_boxed_1361_ = lean_unbox(v_firstDay_1359_);
v_res_1362_ = l_Std_Time_PlainDateTime_weekYear(v_date_1358_, v_firstDay_boxed_1361_, v_minDays_1360_);
lean_dec(v_minDays_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1363_){
_start:
{
lean_object* v_date_1364_; lean_object* v___x_1365_; 
v_date_1364_ = lean_ctor_get(v_date_1363_, 0);
v___x_1365_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1366_);
lean_dec_ref(v_date_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1368_, uint8_t v_firstDay_1369_){
_start:
{
lean_object* v_date_1370_; lean_object* v___x_1371_; 
v_date_1370_ = lean_ctor_get(v_date_1368_, 0);
lean_inc_ref(v_date_1370_);
lean_dec_ref(v_date_1368_);
v___x_1371_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1370_, v_firstDay_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1372_, lean_object* v_firstDay_1373_){
_start:
{
uint8_t v_firstDay_boxed_1374_; lean_object* v_res_1375_; 
v_firstDay_boxed_1374_ = lean_unbox(v_firstDay_1373_);
v_res_1375_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1372_, v_firstDay_boxed_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1376_){
_start:
{
lean_object* v_date_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1400_; 
v_date_1377_ = lean_ctor_get(v_date_1376_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_date_1376_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_date_1376_, 1);
lean_dec(v_unused_1401_);
v___x_1379_ = v_date_1376_;
v_isShared_1380_ = v_isSharedCheck_1400_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_date_1377_);
lean_dec(v_date_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1400_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_year_1381_; lean_object* v_month_1382_; lean_object* v_day_1383_; uint8_t v___y_1385_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_year_1381_ = lean_ctor_get(v_date_1377_, 0);
lean_inc(v_year_1381_);
v_month_1382_ = lean_ctor_get(v_date_1377_, 1);
lean_inc(v_month_1382_);
v_day_1383_ = lean_ctor_get(v_date_1377_, 2);
lean_inc(v_day_1383_);
lean_dec_ref(v_date_1377_);
v___x_1390_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1391_ = lean_int_mod(v_year_1381_, v___x_1390_);
v___x_1392_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1393_ = lean_int_dec_eq(v___x_1391_, v___x_1392_);
lean_dec(v___x_1391_);
if (v___x_1393_ == 0)
{
lean_dec(v_year_1381_);
v___y_1385_ = v___x_1393_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1395_ = lean_int_mod(v_year_1381_, v___x_1394_);
v___x_1396_ = lean_int_dec_eq(v___x_1395_, v___x_1392_);
lean_dec(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec(v_year_1381_);
v___y_1385_ = v___x_1393_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1398_ = lean_int_mod(v_year_1381_, v___x_1397_);
lean_dec(v_year_1381_);
v___x_1399_ = lean_int_dec_eq(v___x_1398_, v___x_1392_);
lean_dec(v___x_1398_);
v___y_1385_ = v___x_1399_;
goto v___jp_1384_;
}
}
v___jp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v_day_1383_);
lean_ctor_set(v___x_1379_, 0, v_month_1382_);
v___x_1387_ = v___x_1379_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_month_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_day_1383_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Std_Time_ValidDate_dayOfYear(v___y_1385_, v___x_1387_);
lean_dec_ref(v___x_1387_);
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object* v_date_1402_){
_start:
{
lean_object* v_date_1403_; lean_object* v___x_1404_; 
v_date_1403_ = lean_ctor_get(v_date_1402_, 0);
v___x_1404_ = l_Std_Time_PlainDate_quarter(v_date_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object* v_date_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_Time_PlainDateTime_quarter(v_date_1405_);
lean_dec_ref(v_date_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object* v_date_1407_, lean_object* v_time_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_date_1407_);
lean_ctor_set(v___x_1409_, 1, v_time_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object* v_time_1410_, lean_object* v_date_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_date_1411_);
lean_ctor_set(v___x_1412_, 1, v_time_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object* v_x_1441_, lean_object* v_y_1442_){
_start:
{
lean_object* v_second_1443_; lean_object* v_nano_1444_; lean_object* v___x_1445_; lean_object* v_second_1446_; lean_object* v_nano_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_nanos_1450_; lean_object* v___x_1451_; lean_object* v_second_1452_; lean_object* v_nano_1453_; lean_object* v___x_1454_; lean_object* v_nanos_1455_; lean_object* v___x_1456_; lean_object* v_nanos_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_second_1443_ = lean_ctor_get(v_y_1442_, 0);
v_nano_1444_ = lean_ctor_get(v_y_1442_, 1);
v___x_1445_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1441_);
v_second_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_second_1446_);
v_nano_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_nano_1447_);
lean_dec_ref(v___x_1445_);
v___x_1448_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1449_ = lean_int_mul(v_second_1443_, v___x_1448_);
v_nanos_1450_ = lean_int_add(v___x_1449_, v_nano_1444_);
lean_dec(v___x_1449_);
v___x_1451_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1450_);
lean_dec(v_nanos_1450_);
v_second_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_second_1452_);
v_nano_1453_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_nano_1453_);
lean_dec_ref(v___x_1451_);
v___x_1454_ = lean_int_mul(v_second_1446_, v___x_1448_);
lean_dec(v_second_1446_);
v_nanos_1455_ = lean_int_add(v___x_1454_, v_nano_1447_);
lean_dec(v_nano_1447_);
lean_dec(v___x_1454_);
v___x_1456_ = lean_int_mul(v_second_1452_, v___x_1448_);
lean_dec(v_second_1452_);
v_nanos_1457_ = lean_int_add(v___x_1456_, v_nano_1453_);
lean_dec(v_nano_1453_);
lean_dec(v___x_1456_);
v___x_1458_ = lean_int_add(v_nanos_1455_, v_nanos_1457_);
lean_dec(v_nanos_1457_);
lean_dec(v_nanos_1455_);
v___x_1459_ = l_Std_Time_Duration_ofNanoseconds(v___x_1458_);
lean_dec(v___x_1458_);
v___x_1460_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1461_, lean_object* v_y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_1461_, v_y_1462_);
lean_dec_ref(v_y_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = l_Std_Time_PlainTime_midnight;
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_date_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_1469_){
_start:
{
lean_object* v_date_1470_; 
v_date_1470_ = lean_ctor_get(v_pdt_1469_, 0);
lean_inc_ref(v_date_1470_);
return v_date_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_1471_);
lean_dec_ref(v_pdt_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_1473_){
_start:
{
lean_object* v_time_1474_; 
v_time_1474_ = lean_ctor_get(v_pdt_1473_, 1);
lean_inc_ref(v_time_1474_);
return v_time_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_1475_);
lean_dec_ref(v_pdt_1475_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_1477_, lean_object* v_y_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v_second_1480_; lean_object* v_nano_1481_; lean_object* v___x_1482_; lean_object* v_second_1483_; lean_object* v_nano_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_nanos_1489_; lean_object* v___x_1490_; lean_object* v_nanos_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1479_ = l_Std_Time_PlainDateTime_toWallTime(v_y_1478_);
v_second_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_second_1480_);
v_nano_1481_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_nano_1481_);
lean_dec_ref(v___x_1479_);
v___x_1482_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1477_);
v_second_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_second_1483_);
v_nano_1484_ = lean_ctor_get(v___x_1482_, 1);
lean_inc(v_nano_1484_);
lean_dec_ref(v___x_1482_);
v___x_1485_ = lean_int_neg(v_second_1480_);
lean_dec(v_second_1480_);
v___x_1486_ = lean_int_neg(v_nano_1481_);
lean_dec(v_nano_1481_);
v___x_1487_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1488_ = lean_int_mul(v_second_1483_, v___x_1487_);
lean_dec(v_second_1483_);
v_nanos_1489_ = lean_int_add(v___x_1488_, v_nano_1484_);
lean_dec(v_nano_1484_);
lean_dec(v___x_1488_);
v___x_1490_ = lean_int_mul(v___x_1485_, v___x_1487_);
lean_dec(v___x_1485_);
v_nanos_1491_ = lean_int_add(v___x_1490_, v___x_1486_);
lean_dec(v___x_1486_);
lean_dec(v___x_1490_);
v___x_1492_ = lean_int_add(v_nanos_1489_, v_nanos_1491_);
lean_dec(v_nanos_1491_);
lean_dec(v_nanos_1489_);
v___x_1493_ = l_Std_Time_Duration_ofNanoseconds(v___x_1492_);
lean_dec(v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object* v_pd_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1497_ = l_Std_Time_PlainDate_toEpochDay(v_pd_1496_);
v___x_1498_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1499_ = lean_int_mul(v___x_1497_, v___x_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object* v_wt_1502_){
_start:
{
lean_object* v_second_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_second_1503_ = lean_ctor_get(v_wt_1502_, 0);
v___x_1504_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1505_ = lean_int_div(v_second_1503_, v___x_1504_);
v___x_1506_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1505_);
lean_dec(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object* v_wt_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Std_Time_PlainDate_ofWallTime(v_wt_1507_);
lean_dec_ref(v_wt_1507_);
return v_res_1508_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1510_ = lean_int_neg(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_1511_, lean_object* v_y_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_nanos_1523_; lean_object* v___x_1524_; lean_object* v_nanos_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1513_ = l_Std_Time_PlainDate_toEpochDay(v_x_1511_);
v___x_1514_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1515_ = lean_int_mul(v___x_1513_, v___x_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1517_ = l_Std_Time_PlainDate_toEpochDay(v_y_1512_);
v___x_1518_ = lean_int_mul(v___x_1517_, v___x_1514_);
lean_dec(v___x_1517_);
v___x_1519_ = lean_int_neg(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
v___x_1521_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1522_ = lean_int_mul(v___x_1515_, v___x_1521_);
lean_dec(v___x_1515_);
v_nanos_1523_ = lean_int_add(v___x_1522_, v___x_1516_);
lean_dec(v___x_1522_);
v___x_1524_ = lean_int_mul(v___x_1519_, v___x_1521_);
lean_dec(v___x_1519_);
v_nanos_1525_ = lean_int_add(v___x_1524_, v___x_1520_);
lean_dec(v___x_1524_);
v___x_1526_ = lean_int_add(v_nanos_1523_, v_nanos_1525_);
lean_dec(v_nanos_1525_);
lean_dec(v_nanos_1523_);
v___x_1527_ = l_Std_Time_Duration_ofNanoseconds(v___x_1526_);
lean_dec(v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object* v_date_1530_, lean_object* v_time_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_date_1530_);
lean_ctor_set(v___x_1532_, 1, v_time_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object* v_pt_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1533_);
v___x_1535_ = l_Std_Time_Duration_ofNanoseconds(v___x_1534_);
lean_dec(v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object* v_pt_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_Time_PlainTime_toWallTime(v_pt_1536_);
lean_dec_ref(v_pt_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object* v_wt_1538_){
_start:
{
lean_object* v_second_1539_; lean_object* v_nano_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_nanos_1543_; lean_object* v___x_1544_; 
v_second_1539_ = lean_ctor_get(v_wt_1538_, 0);
v_nano_1540_ = lean_ctor_get(v_wt_1538_, 1);
v___x_1541_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1542_ = lean_int_mul(v_second_1539_, v___x_1541_);
v_nanos_1543_ = lean_int_add(v___x_1542_, v_nano_1540_);
lean_dec(v___x_1542_);
v___x_1544_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1543_);
lean_dec(v_nanos_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object* v_wt_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_Time_PlainTime_ofWallTime(v_wt_1545_);
lean_dec_ref(v_wt_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object* v_time_1547_, lean_object* v_date_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_date_1548_);
lean_ctor_set(v___x_1549_, 1, v_time_1547_);
return v___x_1549_;
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
