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
lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; lean_object* v_second_383_; lean_object* v_nano_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_531_; 
v_second_383_ = lean_ctor_get(v_stamp_361_, 0);
v_nano_384_ = lean_ctor_get(v_stamp_361_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_stamp_361_);
if (v_isSharedCheck_531_ == 0)
{
v___x_386_ = v_stamp_361_;
v_isShared_387_ = v_isSharedCheck_531_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_nano_384_);
lean_inc(v_second_383_);
lean_dec(v_stamp_361_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_531_;
goto v_resetjp_385_;
}
v___jp_362_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v___y_363_);
lean_ctor_set(v___x_368_, 1, v___y_366_);
lean_ctor_set(v___x_368_, 2, v___y_364_);
lean_ctor_set(v___x_368_, 3, v___y_365_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___y_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
v___jp_370_:
{
lean_object* v_max_379_; uint8_t v___x_380_; 
v_max_379_ = l_Std_Time_Month_Ordinal_days(v___y_378_, v___y_371_);
v___x_380_ = lean_int_dec_lt(v_max_379_, v___y_374_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_max_379_);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v___y_372_);
lean_ctor_set(v___x_381_, 1, v___y_371_);
lean_ctor_set(v___x_381_, 2, v___y_374_);
v___y_363_ = v___y_373_;
v___y_364_ = v___y_375_;
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
lean_ctor_set(v___x_382_, 0, v___y_372_);
lean_ctor_set(v___x_382_, 1, v___y_371_);
lean_ctor_set(v___x_382_, 2, v_max_379_);
v___y_363_ = v___y_373_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_377_;
v___y_366_ = v___y_376_;
v___y_367_ = v___x_382_;
goto v___jp_362_;
}
}
v_resetjp_385_:
{
lean_object* v_leapYearEpoch_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v_daysPer400Y_402_; lean_object* v___x_403_; lean_object* v_daysPer100Y_404_; lean_object* v___x_405_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_daysPer4Y_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v_hmon_430_; lean_object* v_year_431_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v_remYears_448_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_quadrennialCycles_483_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_centenialCycles_493_; lean_object* v___y_501_; lean_object* v_quadracentennialCycles_502_; lean_object* v_remDays_503_; lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v_snd_517_; lean_object* v_secs_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_leapYearEpoch_388_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__0, &l_Std_Time_PlainDateTime_ofWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0);
v___x_389_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_390_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v_daysPer400Y_402_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__5, &l_Std_Time_PlainDateTime_ofWallTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5);
v___x_403_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v_daysPer100Y_404_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__9, &l_Std_Time_PlainDateTime_ofWallTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9);
v___x_405_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v_daysPer4Y_422_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__12, &l_Std_Time_PlainDateTime_ofWallTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12);
v___x_423_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_424_ = lean_int_mul(v_second_383_, v___x_423_);
lean_dec(v_second_383_);
v___x_425_ = lean_int_add(v___x_424_, v_nano_384_);
lean_dec(v_nano_384_);
lean_dec(v___x_424_);
v_secs_526_ = lean_int_div(v___x_425_, v___x_423_);
v___x_527_ = lean_int_mod(v___x_425_, v___x_423_);
v___x_528_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_529_ = lean_int_dec_lt(v___x_527_, v___x_528_);
lean_dec(v___x_527_);
if (v___x_529_ == 0)
{
v_snd_517_ = v_secs_526_;
goto v___jp_516_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_int_sub(v_secs_526_, v___x_421_);
lean_dec(v_secs_526_);
v_snd_517_ = v___x_530_;
goto v___jp_516_;
}
v___jp_391_:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_int_mod(v___y_394_, v___x_390_);
v___x_401_ = lean_int_dec_eq(v___x_400_, v___y_392_);
lean_dec(v___y_392_);
lean_dec(v___x_400_);
v___y_371_ = v___y_393_;
v___y_372_ = v___y_394_;
v___y_373_ = v___y_395_;
v___y_374_ = v___y_396_;
v___y_375_ = v___y_397_;
v___y_376_ = v___y_399_;
v___y_377_ = v___y_398_;
v___y_378_ = v___x_401_;
goto v___jp_370_;
}
v___jp_406_:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_int_mod(v___y_408_, v___x_405_);
v___x_416_ = lean_nat_to_int(v___y_411_);
v___x_417_ = lean_int_dec_eq(v___x_415_, v___x_416_);
lean_dec(v___x_415_);
if (v___x_417_ == 0)
{
lean_dec(v___x_416_);
v___y_371_ = v___y_407_;
v___y_372_ = v___y_408_;
v___y_373_ = v___y_409_;
v___y_374_ = v___y_414_;
v___y_375_ = v___y_410_;
v___y_376_ = v___y_413_;
v___y_377_ = v___y_412_;
v___y_378_ = v___x_417_;
goto v___jp_370_;
}
else
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_int_mod(v___y_408_, v___x_403_);
v___x_419_ = lean_int_dec_eq(v___x_418_, v___x_416_);
lean_dec(v___x_418_);
if (v___x_419_ == 0)
{
if (v___x_417_ == 0)
{
v___y_392_ = v___x_416_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_414_;
v___y_397_ = v___y_410_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_413_;
goto v___jp_391_;
}
else
{
lean_dec(v___x_416_);
v___y_371_ = v___y_407_;
v___y_372_ = v___y_408_;
v___y_373_ = v___y_409_;
v___y_374_ = v___y_414_;
v___y_375_ = v___y_410_;
v___y_376_ = v___y_413_;
v___y_377_ = v___y_412_;
v___y_378_ = v___x_417_;
goto v___jp_370_;
}
}
else
{
v___y_392_ = v___x_416_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_414_;
v___y_397_ = v___y_410_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_413_;
goto v___jp_391_;
}
}
}
v___jp_426_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_432_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__13, &l_Std_Time_PlainDateTime_ofWallTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13);
v___x_433_ = lean_int_emod(v___y_428_, v___x_432_);
v___x_434_ = lean_int_ediv(v___y_428_, v___x_432_);
v___x_435_ = lean_int_emod(v___x_434_, v___x_432_);
lean_dec(v___x_434_);
v___x_436_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__14, &l_Std_Time_PlainDateTime_ofWallTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14);
v___x_437_ = lean_int_ediv(v___y_428_, v___x_436_);
lean_dec(v___y_428_);
v___x_438_ = lean_int_emod(v___x_425_, v___x_423_);
lean_dec(v___x_425_);
v___x_439_ = l_Fin_succ___redArg(v___y_427_);
lean_dec(v___y_427_);
v___x_440_ = lean_nat_dec_le(v___x_420_, v___x_439_);
if (v___x_440_ == 0)
{
lean_dec(v___x_439_);
v___y_407_ = v_hmon_430_;
v___y_408_ = v_year_431_;
v___y_409_ = v___x_437_;
v___y_410_ = v___x_433_;
v___y_411_ = v___y_429_;
v___y_412_ = v___x_438_;
v___y_413_ = v___x_435_;
v___y_414_ = v___x_421_;
goto v___jp_406_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_nat_to_int(v___x_439_);
v___y_407_ = v_hmon_430_;
v___y_408_ = v_year_431_;
v___y_409_ = v___x_437_;
v___y_410_ = v___x_433_;
v___y_411_ = v___y_429_;
v___y_412_ = v___x_438_;
v___y_413_ = v___x_435_;
v___y_414_ = v___x_441_;
goto v___jp_406_;
}
}
v___jp_442_:
{
lean_object* v___x_449_; lean_object* v_remDays_450_; lean_object* v___x_451_; lean_object* v_months_452_; lean_object* v_mon_453_; lean_object* v___x_455_; 
v___x_449_ = lean_int_mul(v_remYears_448_, v___x_389_);
v_remDays_450_ = lean_int_sub(v___y_446_, v___x_449_);
lean_dec(v___x_449_);
lean_dec(v___y_446_);
v___x_451_ = lean_unsigned_to_nat(31u);
v_months_452_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__28, &l_Std_Time_PlainDateTime_ofWallTime___closed__28_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28);
v_mon_453_ = lean_unsigned_to_nat(0u);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_mon_453_);
lean_ctor_set(v___x_386_, 0, v_remDays_450_);
v___x_455_ = v___x_386_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_remDays_450_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_mon_453_);
v___x_455_ = v_reuseFailAlloc_477_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v_fst_457_; lean_object* v_snd_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_year_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_456_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_months_452_, v___x_455_);
v_fst_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_fst_457_);
v_snd_458_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_snd_458_);
lean_dec_ref(v___x_456_);
v___x_459_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__29, &l_Std_Time_PlainDateTime_ofWallTime___closed__29_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29);
v___x_460_ = lean_int_add(v___x_459_, v_remYears_448_);
lean_dec(v_remYears_448_);
v___x_461_ = lean_int_mul(v___x_405_, v___y_444_);
lean_dec(v___y_444_);
v___x_462_ = lean_int_add(v___x_460_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_int_mul(v___x_403_, v___y_447_);
lean_dec(v___y_447_);
v___x_464_ = lean_int_add(v___x_462_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_int_mul(v___x_390_, v___y_445_);
lean_dec(v___y_445_);
v_year_466_ = lean_int_add(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
v___x_467_ = l_Int_toNat(v_fst_457_);
lean_dec(v_fst_457_);
v___x_468_ = lean_nat_mod(v___x_467_, v___x_451_);
lean_dec(v___x_467_);
v___x_469_ = lean_unsigned_to_nat(10u);
v___x_470_ = lean_nat_dec_lt(v___x_469_, v_snd_458_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_unsigned_to_nat(2u);
v___x_472_ = lean_nat_add(v_snd_458_, v___x_471_);
lean_dec(v_snd_458_);
v___x_473_ = lean_nat_to_int(v___x_472_);
v___y_427_ = v___x_468_;
v___y_428_ = v___y_443_;
v___y_429_ = v_mon_453_;
v_hmon_430_ = v___x_473_;
v_year_431_ = v_year_466_;
goto v___jp_426_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_int_add(v_year_466_, v___x_421_);
lean_dec(v_year_466_);
v___x_475_ = lean_nat_sub(v_snd_458_, v___x_469_);
lean_dec(v_snd_458_);
v___x_476_ = lean_nat_to_int(v___x_475_);
v___y_427_ = v___x_468_;
v___y_428_ = v___y_443_;
v___y_429_ = v_mon_453_;
v_hmon_430_ = v___x_476_;
v_year_431_ = v___x_474_;
goto v___jp_426_;
}
}
}
v___jp_478_:
{
lean_object* v___x_484_; lean_object* v_remDays_485_; lean_object* v_remYears_486_; uint8_t v___x_487_; 
v___x_484_ = lean_int_mul(v_quadrennialCycles_483_, v_daysPer4Y_422_);
v_remDays_485_ = lean_int_sub(v___y_479_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___y_479_);
v_remYears_486_ = lean_int_ediv(v_remDays_485_, v___x_389_);
v___x_487_ = lean_int_dec_eq(v_remYears_486_, v___x_405_);
if (v___x_487_ == 0)
{
v___y_443_ = v___y_480_;
v___y_444_ = v_quadrennialCycles_483_;
v___y_445_ = v___y_481_;
v___y_446_ = v_remDays_485_;
v___y_447_ = v___y_482_;
v_remYears_448_ = v_remYears_486_;
goto v___jp_442_;
}
else
{
lean_object* v_remYears_488_; 
v_remYears_488_ = lean_int_sub(v_remYears_486_, v___x_421_);
lean_dec(v_remYears_486_);
v___y_443_ = v___y_480_;
v___y_444_ = v_quadrennialCycles_483_;
v___y_445_ = v___y_481_;
v___y_446_ = v_remDays_485_;
v___y_447_ = v___y_482_;
v_remYears_448_ = v_remYears_488_;
goto v___jp_442_;
}
}
v___jp_489_:
{
lean_object* v___x_494_; lean_object* v_remDays_495_; lean_object* v_quadrennialCycles_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_494_ = lean_int_mul(v_centenialCycles_493_, v_daysPer100Y_404_);
v_remDays_495_ = lean_int_sub(v___y_491_, v___x_494_);
lean_dec(v___x_494_);
lean_dec(v___y_491_);
v_quadrennialCycles_496_ = lean_int_ediv(v_remDays_495_, v_daysPer4Y_422_);
v___x_497_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__30, &l_Std_Time_PlainDateTime_ofWallTime___closed__30_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30);
v___x_498_ = lean_int_dec_eq(v_quadrennialCycles_496_, v___x_497_);
if (v___x_498_ == 0)
{
v___y_479_ = v_remDays_495_;
v___y_480_ = v___y_490_;
v___y_481_ = v___y_492_;
v___y_482_ = v_centenialCycles_493_;
v_quadrennialCycles_483_ = v_quadrennialCycles_496_;
goto v___jp_478_;
}
else
{
lean_object* v_quadrennialCycles_499_; 
v_quadrennialCycles_499_ = lean_int_sub(v_quadrennialCycles_496_, v___x_421_);
lean_dec(v_quadrennialCycles_496_);
v___y_479_ = v_remDays_495_;
v___y_480_ = v___y_490_;
v___y_481_ = v___y_492_;
v___y_482_ = v_centenialCycles_493_;
v_quadrennialCycles_483_ = v_quadrennialCycles_499_;
goto v___jp_478_;
}
}
v___jp_500_:
{
lean_object* v_centenialCycles_504_; uint8_t v___x_505_; 
v_centenialCycles_504_ = lean_int_ediv(v_remDays_503_, v_daysPer100Y_404_);
v___x_505_ = lean_int_dec_eq(v_centenialCycles_504_, v___x_405_);
if (v___x_505_ == 0)
{
v___y_490_ = v___y_501_;
v___y_491_ = v_remDays_503_;
v___y_492_ = v_quadracentennialCycles_502_;
v_centenialCycles_493_ = v_centenialCycles_504_;
goto v___jp_489_;
}
else
{
lean_object* v_centenialCycles_506_; 
v_centenialCycles_506_ = lean_int_sub(v_centenialCycles_504_, v___x_421_);
lean_dec(v_centenialCycles_504_);
v___y_490_ = v___y_501_;
v___y_491_ = v_remDays_503_;
v___y_492_ = v_quadracentennialCycles_502_;
v_centenialCycles_493_ = v_centenialCycles_506_;
goto v___jp_489_;
}
}
v___jp_507_:
{
lean_object* v_quadracentennialCycles_510_; lean_object* v_remDays_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_quadracentennialCycles_510_ = lean_int_ediv(v_snd_509_, v_daysPer400Y_402_);
v_remDays_511_ = lean_int_emod(v_snd_509_, v_daysPer400Y_402_);
lean_dec(v_snd_509_);
v___x_512_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_513_ = lean_int_dec_lt(v_remDays_511_, v___x_512_);
if (v___x_513_ == 0)
{
v___y_501_ = v_fst_508_;
v_quadracentennialCycles_502_ = v_quadracentennialCycles_510_;
v_remDays_503_ = v_remDays_511_;
goto v___jp_500_;
}
else
{
lean_object* v_remDays_514_; lean_object* v_quadracentennialCycles_515_; 
v_remDays_514_ = lean_int_add(v_remDays_511_, v_daysPer400Y_402_);
lean_dec(v_remDays_511_);
v_quadracentennialCycles_515_ = lean_int_sub(v_quadracentennialCycles_510_, v___x_421_);
lean_dec(v_quadracentennialCycles_510_);
v___y_501_ = v_fst_508_;
v_quadracentennialCycles_502_ = v_quadracentennialCycles_515_;
v_remDays_503_ = v_remDays_514_;
goto v___jp_500_;
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v_boundedDaysSinceEpoch_519_; lean_object* v_rawDays_520_; lean_object* v_h_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_518_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v_boundedDaysSinceEpoch_519_ = lean_int_div(v_snd_517_, v___x_518_);
v_rawDays_520_ = lean_int_sub(v_boundedDaysSinceEpoch_519_, v_leapYearEpoch_388_);
lean_dec(v_boundedDaysSinceEpoch_519_);
v_h_521_ = lean_int_mod(v_snd_517_, v___x_518_);
lean_dec(v_snd_517_);
v___x_522_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__31, &l_Std_Time_PlainDateTime_ofWallTime___closed__31_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31);
v___x_523_ = lean_int_dec_le(v_h_521_, v___x_522_);
if (v___x_523_ == 0)
{
v_fst_508_ = v_h_521_;
v_snd_509_ = v_rawDays_520_;
goto v___jp_507_;
}
else
{
lean_object* v___x_524_; lean_object* v_rawDays_525_; 
v___x_524_ = lean_int_add(v_h_521_, v___x_518_);
lean_dec(v_h_521_);
v_rawDays_525_ = lean_int_sub(v_rawDays_520_, v___x_421_);
lean_dec(v_rawDays_520_);
v_fst_508_ = v___x_524_;
v_snd_509_ = v_rawDays_525_;
goto v___jp_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(lean_object* v_as_532_, lean_object* v_as_x27_533_, lean_object* v_b_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_533_, v_b_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(lean_object* v_as_537_, lean_object* v_as_x27_538_, lean_object* v_b_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(v_as_537_, v_as_x27_538_, v_b_539_, v_a_540_);
lean_dec(v_as_x27_538_);
lean_dec(v_as_537_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object* v_pdt_542_){
_start:
{
lean_object* v_date_543_; lean_object* v___x_544_; 
v_date_543_ = lean_ctor_get(v_pdt_542_, 0);
lean_inc_ref(v_date_543_);
lean_dec_ref(v_pdt_542_);
v___x_544_ = l_Std_Time_PlainDate_toEpochDay(v_date_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object* v_days_545_, lean_object* v_time_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = l_Std_Time_PlainDate_ofEpochDay(v_days_545_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_time_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object* v_days_549_, lean_object* v_time_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_549_, v_time_550_);
lean_dec(v_days_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_552_, uint8_t v_desiredWeekday_553_){
_start:
{
lean_object* v_date_554_; lean_object* v_time_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_date_554_ = lean_ctor_get(v_dt_552_, 0);
v_time_555_ = lean_ctor_get(v_dt_552_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_dt_552_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v_dt_552_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_time_555_);
lean_inc(v_date_554_);
lean_dec(v_dt_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = l_Std_Time_PlainDate_withWeekday(v_date_554_, v_desiredWeekday_553_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_time_555_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_564_, lean_object* v_desiredWeekday_565_){
_start:
{
uint8_t v_desiredWeekday_boxed_566_; lean_object* v_res_567_; 
v_desiredWeekday_boxed_566_ = lean_unbox(v_desiredWeekday_565_);
v_res_567_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_564_, v_desiredWeekday_boxed_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_568_, lean_object* v_days_569_){
_start:
{
lean_object* v_date_570_; lean_object* v_time_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_609_; 
v_date_570_ = lean_ctor_get(v_dt_568_, 0);
v_time_571_ = lean_ctor_get(v_dt_568_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_dt_568_);
if (v_isSharedCheck_609_ == 0)
{
v___x_573_ = v_dt_568_;
v_isShared_574_ = v_isSharedCheck_609_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_time_571_);
lean_inc(v_date_570_);
lean_dec(v_dt_568_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_609_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_year_575_; lean_object* v_month_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_607_; 
v_year_575_ = lean_ctor_get(v_date_570_, 0);
v_month_576_ = lean_ctor_get(v_date_570_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_date_570_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_date_570_, 2);
lean_dec(v_unused_608_);
v___x_578_ = v_date_570_;
v_isShared_579_ = v_isSharedCheck_607_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_month_576_);
lean_inc(v_year_575_);
lean_dec(v_date_570_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_607_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v___y_581_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_603_; 
v___x_596_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_597_ = lean_int_mod(v_year_575_, v___x_596_);
v___x_598_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_603_ = lean_int_dec_eq(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
if (v___x_603_ == 0)
{
v___y_581_ = v___x_603_;
goto v___jp_580_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_605_ = lean_int_mod(v_year_575_, v___x_604_);
v___x_606_ = lean_int_dec_eq(v___x_605_, v___x_598_);
lean_dec(v___x_605_);
if (v___x_606_ == 0)
{
if (v___x_603_ == 0)
{
goto v___jp_599_;
}
else
{
v___y_581_ = v___x_603_;
goto v___jp_580_;
}
}
else
{
goto v___jp_599_;
}
}
v___jp_580_:
{
lean_object* v_max_582_; uint8_t v___x_583_; 
v_max_582_ = l_Std_Time_Month_Ordinal_days(v___y_581_, v_month_576_);
v___x_583_ = lean_int_dec_lt(v_max_582_, v_days_569_);
if (v___x_583_ == 0)
{
lean_object* v___x_585_; 
lean_dec(v_max_582_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 2, v_days_569_);
v___x_585_ = v___x_578_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_year_575_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_month_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_days_569_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_585_);
v___x_587_ = v___x_573_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_time_571_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec(v_days_569_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 2, v_max_582_);
v___x_591_ = v___x_578_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_year_575_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_month_576_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_max_582_);
v___x_591_ = v_reuseFailAlloc_595_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_591_);
v___x_593_ = v___x_573_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_time_571_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
v___jp_599_:
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_601_ = lean_int_mod(v_year_575_, v___x_600_);
v___x_602_ = lean_int_dec_eq(v___x_601_, v___x_598_);
lean_dec(v___x_601_);
v___y_581_ = v___x_602_;
goto v___jp_580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_610_, lean_object* v_days_611_){
_start:
{
lean_object* v_date_612_; lean_object* v_time_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_623_; 
v_date_612_ = lean_ctor_get(v_dt_610_, 0);
v_time_613_ = lean_ctor_get(v_dt_610_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_dt_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_615_ = v_dt_610_;
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_time_613_);
lean_inc(v_date_612_);
lean_dec(v_dt_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_year_617_; lean_object* v_month_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v_year_617_ = lean_ctor_get(v_date_612_, 0);
lean_inc(v_year_617_);
v_month_618_ = lean_ctor_get(v_date_612_, 1);
lean_inc(v_month_618_);
lean_dec_ref(v_date_612_);
v___x_619_ = l_Std_Time_PlainDate_rollOver(v_year_617_, v_month_618_, v_days_611_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_619_);
v___x_621_ = v___x_615_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_time_613_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_624_, lean_object* v_days_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_624_, v_days_625_);
lean_dec(v_days_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_627_, lean_object* v_month_628_){
_start:
{
lean_object* v_date_629_; lean_object* v_time_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_668_; 
v_date_629_ = lean_ctor_get(v_dt_627_, 0);
v_time_630_ = lean_ctor_get(v_dt_627_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_dt_627_);
if (v_isSharedCheck_668_ == 0)
{
v___x_632_ = v_dt_627_;
v_isShared_633_ = v_isSharedCheck_668_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_time_630_);
lean_inc(v_date_629_);
lean_dec(v_dt_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_668_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_year_634_; lean_object* v_day_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_666_; 
v_year_634_ = lean_ctor_get(v_date_629_, 0);
v_day_635_ = lean_ctor_get(v_date_629_, 2);
v_isSharedCheck_666_ = !lean_is_exclusive(v_date_629_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_date_629_, 1);
lean_dec(v_unused_667_);
v___x_637_ = v_date_629_;
v_isShared_638_ = v_isSharedCheck_666_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_day_635_);
lean_inc(v_year_634_);
lean_dec(v_date_629_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_666_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v___y_640_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_662_; 
v___x_655_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_656_ = lean_int_mod(v_year_634_, v___x_655_);
v___x_657_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_662_ = lean_int_dec_eq(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
if (v___x_662_ == 0)
{
v___y_640_ = v___x_662_;
goto v___jp_639_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_664_ = lean_int_mod(v_year_634_, v___x_663_);
v___x_665_ = lean_int_dec_eq(v___x_664_, v___x_657_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
if (v___x_662_ == 0)
{
goto v___jp_658_;
}
else
{
v___y_640_ = v___x_662_;
goto v___jp_639_;
}
}
else
{
goto v___jp_658_;
}
}
v___jp_639_:
{
lean_object* v_max_641_; uint8_t v___x_642_; 
v_max_641_ = l_Std_Time_Month_Ordinal_days(v___y_640_, v_month_628_);
v___x_642_ = lean_int_dec_lt(v_max_641_, v_day_635_);
if (v___x_642_ == 0)
{
lean_object* v___x_644_; 
lean_dec(v_max_641_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_month_628_);
v___x_644_ = v___x_637_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_year_634_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_month_628_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_day_635_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_644_);
v___x_646_ = v___x_632_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_time_630_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v_day_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 2, v_max_641_);
lean_ctor_set(v___x_637_, 1, v_month_628_);
v___x_650_ = v___x_637_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_year_634_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_month_628_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_max_641_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_650_);
v___x_652_ = v___x_632_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_time_630_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
v___jp_658_:
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_660_ = lean_int_mod(v_year_634_, v___x_659_);
v___x_661_ = lean_int_dec_eq(v___x_660_, v___x_657_);
lean_dec(v___x_660_);
v___y_640_ = v___x_661_;
goto v___jp_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_669_, lean_object* v_month_670_){
_start:
{
lean_object* v_date_671_; lean_object* v_time_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
v_date_671_ = lean_ctor_get(v_dt_669_, 0);
v_time_672_ = lean_ctor_get(v_dt_669_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_dt_669_);
if (v_isSharedCheck_682_ == 0)
{
v___x_674_ = v_dt_669_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_time_672_);
lean_inc(v_date_671_);
lean_dec(v_dt_669_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_year_676_; lean_object* v_day_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v_year_676_ = lean_ctor_get(v_date_671_, 0);
lean_inc(v_year_676_);
v_day_677_ = lean_ctor_get(v_date_671_, 2);
lean_inc(v_day_677_);
lean_dec_ref(v_date_671_);
v___x_678_ = l_Std_Time_PlainDate_rollOver(v_year_676_, v_month_670_, v_day_677_);
lean_dec(v_day_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_678_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_time_672_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_683_, lean_object* v_year_684_){
_start:
{
lean_object* v_date_685_; lean_object* v_time_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_724_; 
v_date_685_ = lean_ctor_get(v_dt_683_, 0);
v_time_686_ = lean_ctor_get(v_dt_683_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_dt_683_);
if (v_isSharedCheck_724_ == 0)
{
v___x_688_ = v_dt_683_;
v_isShared_689_ = v_isSharedCheck_724_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_time_686_);
lean_inc(v_date_685_);
lean_dec(v_dt_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_724_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_month_690_; lean_object* v_day_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_722_; 
v_month_690_ = lean_ctor_get(v_date_685_, 1);
v_day_691_ = lean_ctor_get(v_date_685_, 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_date_685_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_date_685_, 0);
lean_dec(v_unused_723_);
v___x_693_ = v_date_685_;
v_isShared_694_ = v_isSharedCheck_722_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_day_691_);
lean_inc(v_month_690_);
lean_dec(v_date_685_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_722_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
uint8_t v___y_696_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_718_; 
v___x_711_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_712_ = lean_int_mod(v_year_684_, v___x_711_);
v___x_713_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_718_ = lean_int_dec_eq(v___x_712_, v___x_713_);
lean_dec(v___x_712_);
if (v___x_718_ == 0)
{
v___y_696_ = v___x_718_;
goto v___jp_695_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_720_ = lean_int_mod(v_year_684_, v___x_719_);
v___x_721_ = lean_int_dec_eq(v___x_720_, v___x_713_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
if (v___x_718_ == 0)
{
goto v___jp_714_;
}
else
{
v___y_696_ = v___x_718_;
goto v___jp_695_;
}
}
else
{
goto v___jp_714_;
}
}
v___jp_695_:
{
lean_object* v_max_697_; uint8_t v___x_698_; 
v_max_697_ = l_Std_Time_Month_Ordinal_days(v___y_696_, v_month_690_);
v___x_698_ = lean_int_dec_lt(v_max_697_, v_day_691_);
if (v___x_698_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v_max_697_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_year_684_);
v___x_700_ = v___x_693_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_year_684_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_month_690_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_day_691_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_700_);
v___x_702_ = v___x_688_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_time_686_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v_day_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 2, v_max_697_);
lean_ctor_set(v___x_693_, 0, v_year_684_);
v___x_706_ = v___x_693_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_year_684_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_month_690_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_max_697_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_706_);
v___x_708_ = v___x_688_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_time_686_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
v___jp_714_:
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_716_ = lean_int_mod(v_year_684_, v___x_715_);
v___x_717_ = lean_int_dec_eq(v___x_716_, v___x_713_);
lean_dec(v___x_716_);
v___y_696_ = v___x_717_;
goto v___jp_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_725_, lean_object* v_year_726_){
_start:
{
lean_object* v_date_727_; lean_object* v_time_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_738_; 
v_date_727_ = lean_ctor_get(v_dt_725_, 0);
v_time_728_ = lean_ctor_get(v_dt_725_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_dt_725_);
if (v_isSharedCheck_738_ == 0)
{
v___x_730_ = v_dt_725_;
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_time_728_);
lean_inc(v_date_727_);
lean_dec(v_dt_725_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_month_732_; lean_object* v_day_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_month_732_ = lean_ctor_get(v_date_727_, 1);
lean_inc(v_month_732_);
v_day_733_ = lean_ctor_get(v_date_727_, 2);
lean_inc(v_day_733_);
lean_dec_ref(v_date_727_);
v___x_734_ = l_Std_Time_PlainDate_rollOver(v_year_726_, v_month_732_, v_day_733_);
lean_dec(v_day_733_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_time_728_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_739_, lean_object* v_hour_740_){
_start:
{
lean_object* v_time_741_; lean_object* v_date_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_760_; 
v_time_741_ = lean_ctor_get(v_dt_739_, 1);
v_date_742_ = lean_ctor_get(v_dt_739_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_dt_739_);
if (v_isSharedCheck_760_ == 0)
{
v___x_744_ = v_dt_739_;
v_isShared_745_ = v_isSharedCheck_760_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_time_741_);
lean_inc(v_date_742_);
lean_dec(v_dt_739_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_760_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_minute_746_; lean_object* v_second_747_; lean_object* v_nanosecond_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_758_; 
v_minute_746_ = lean_ctor_get(v_time_741_, 1);
v_second_747_ = lean_ctor_get(v_time_741_, 2);
v_nanosecond_748_ = lean_ctor_get(v_time_741_, 3);
v_isSharedCheck_758_ = !lean_is_exclusive(v_time_741_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_time_741_, 0);
lean_dec(v_unused_759_);
v___x_750_ = v_time_741_;
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_nanosecond_748_);
lean_inc(v_second_747_);
lean_inc(v_minute_746_);
lean_dec(v_time_741_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v_hour_740_);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_hour_740_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_minute_746_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_second_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_nanosecond_748_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_753_);
v___x_755_ = v___x_744_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_date_742_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_761_, lean_object* v_minute_762_){
_start:
{
lean_object* v_time_763_; lean_object* v_date_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_782_; 
v_time_763_ = lean_ctor_get(v_dt_761_, 1);
v_date_764_ = lean_ctor_get(v_dt_761_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_dt_761_);
if (v_isSharedCheck_782_ == 0)
{
v___x_766_ = v_dt_761_;
v_isShared_767_ = v_isSharedCheck_782_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_time_763_);
lean_inc(v_date_764_);
lean_dec(v_dt_761_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_782_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_hour_768_; lean_object* v_second_769_; lean_object* v_nanosecond_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_780_; 
v_hour_768_ = lean_ctor_get(v_time_763_, 0);
v_second_769_ = lean_ctor_get(v_time_763_, 2);
v_nanosecond_770_ = lean_ctor_get(v_time_763_, 3);
v_isSharedCheck_780_ = !lean_is_exclusive(v_time_763_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_time_763_, 1);
lean_dec(v_unused_781_);
v___x_772_ = v_time_763_;
v_isShared_773_ = v_isSharedCheck_780_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_nanosecond_770_);
lean_inc(v_second_769_);
lean_inc(v_hour_768_);
lean_dec(v_time_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_780_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_minute_762_);
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_hour_768_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_minute_762_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_second_769_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_nanosecond_770_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_775_);
v___x_777_ = v___x_766_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_date_764_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_783_, lean_object* v_second_784_){
_start:
{
lean_object* v_time_785_; lean_object* v_date_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_804_; 
v_time_785_ = lean_ctor_get(v_dt_783_, 1);
v_date_786_ = lean_ctor_get(v_dt_783_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_dt_783_);
if (v_isSharedCheck_804_ == 0)
{
v___x_788_ = v_dt_783_;
v_isShared_789_ = v_isSharedCheck_804_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_time_785_);
lean_inc(v_date_786_);
lean_dec(v_dt_783_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_804_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_hour_790_; lean_object* v_minute_791_; lean_object* v_nanosecond_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
v_hour_790_ = lean_ctor_get(v_time_785_, 0);
v_minute_791_ = lean_ctor_get(v_time_785_, 1);
v_nanosecond_792_ = lean_ctor_get(v_time_785_, 3);
v_isSharedCheck_802_ = !lean_is_exclusive(v_time_785_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_time_785_, 2);
lean_dec(v_unused_803_);
v___x_794_ = v_time_785_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_nanosecond_792_);
lean_inc(v_minute_791_);
lean_inc(v_hour_790_);
lean_dec(v_time_785_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 2, v_second_784_);
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_hour_790_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_minute_791_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_second_784_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_nanosecond_792_);
v___x_797_ = v_reuseFailAlloc_801_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_797_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_date_786_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_797_);
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
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_unsigned_to_nat(1000u);
v___x_806_ = lean_nat_to_int(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(1000000u);
v___x_808_ = lean_nat_to_int(v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_809_, lean_object* v_millis_810_){
_start:
{
lean_object* v_time_811_; lean_object* v_date_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_835_; 
v_time_811_ = lean_ctor_get(v_dt_809_, 1);
v_date_812_ = lean_ctor_get(v_dt_809_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_dt_809_);
if (v_isSharedCheck_835_ == 0)
{
v___x_814_ = v_dt_809_;
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_time_811_);
lean_inc(v_date_812_);
lean_dec(v_dt_809_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_hour_816_; lean_object* v_minute_817_; lean_object* v_second_818_; lean_object* v_nanosecond_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_834_; 
v_hour_816_ = lean_ctor_get(v_time_811_, 0);
v_minute_817_ = lean_ctor_get(v_time_811_, 1);
v_second_818_ = lean_ctor_get(v_time_811_, 2);
v_nanosecond_819_ = lean_ctor_get(v_time_811_, 3);
v_isSharedCheck_834_ = !lean_is_exclusive(v_time_811_);
if (v_isSharedCheck_834_ == 0)
{
v___x_821_ = v_time_811_;
v_isShared_822_ = v_isSharedCheck_834_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_nanosecond_819_);
lean_inc(v_second_818_);
lean_inc(v_minute_817_);
lean_inc(v_hour_816_);
lean_dec(v_time_811_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_834_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_823_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_824_ = lean_int_emod(v_nanosecond_819_, v___x_823_);
lean_dec(v_nanosecond_819_);
v___x_825_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_826_ = lean_int_mul(v_millis_810_, v___x_825_);
v___x_827_ = lean_int_add(v___x_826_, v___x_824_);
lean_dec(v___x_824_);
lean_dec(v___x_826_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 3, v___x_827_);
v___x_829_ = v___x_821_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_hour_816_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_minute_817_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_second_818_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v___x_827_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_829_);
v___x_831_ = v___x_814_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_date_812_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_836_, lean_object* v_millis_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_836_, v_millis_837_);
lean_dec(v_millis_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_839_, lean_object* v_nano_840_){
_start:
{
lean_object* v_time_841_; lean_object* v_date_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_860_; 
v_time_841_ = lean_ctor_get(v_dt_839_, 1);
v_date_842_ = lean_ctor_get(v_dt_839_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_dt_839_);
if (v_isSharedCheck_860_ == 0)
{
v___x_844_ = v_dt_839_;
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_time_841_);
lean_inc(v_date_842_);
lean_dec(v_dt_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_hour_846_; lean_object* v_minute_847_; lean_object* v_second_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_hour_846_ = lean_ctor_get(v_time_841_, 0);
v_minute_847_ = lean_ctor_get(v_time_841_, 1);
v_second_848_ = lean_ctor_get(v_time_841_, 2);
v_isSharedCheck_858_ = !lean_is_exclusive(v_time_841_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_time_841_, 3);
lean_dec(v_unused_859_);
v___x_850_ = v_time_841_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_second_848_);
lean_inc(v_minute_847_);
lean_inc(v_hour_846_);
lean_dec(v_time_841_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 3, v_nano_840_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_hour_846_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_minute_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_second_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_nano_840_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_853_);
v___x_855_ = v___x_844_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_date_842_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_861_, lean_object* v_days_862_){
_start:
{
lean_object* v_date_863_; lean_object* v_time_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_date_863_ = lean_ctor_get(v_dt_861_, 0);
v_time_864_ = lean_ctor_get(v_dt_861_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_dt_861_);
if (v_isSharedCheck_874_ == 0)
{
v___x_866_ = v_dt_861_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_time_864_);
lean_inc(v_date_863_);
lean_dec(v_dt_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_dateDays_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v_dateDays_868_ = l_Std_Time_PlainDate_toEpochDay(v_date_863_);
v___x_869_ = lean_int_add(v_dateDays_868_, v_days_862_);
lean_dec(v_dateDays_868_);
v___x_870_ = l_Std_Time_PlainDate_ofEpochDay(v___x_869_);
lean_dec(v___x_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_time_864_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_875_, lean_object* v_days_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Time_PlainDateTime_addDays(v_dt_875_, v_days_876_);
lean_dec(v_days_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_878_, lean_object* v_days_879_){
_start:
{
lean_object* v_date_880_; lean_object* v_time_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_892_; 
v_date_880_ = lean_ctor_get(v_dt_878_, 0);
v_time_881_ = lean_ctor_get(v_dt_878_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_dt_878_);
if (v_isSharedCheck_892_ == 0)
{
v___x_883_ = v_dt_878_;
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_time_881_);
lean_inc(v_date_880_);
lean_dec(v_dt_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v_dateDays_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_885_ = lean_int_neg(v_days_879_);
v_dateDays_886_ = l_Std_Time_PlainDate_toEpochDay(v_date_880_);
v___x_887_ = lean_int_add(v_dateDays_886_, v___x_885_);
lean_dec(v___x_885_);
lean_dec(v_dateDays_886_);
v___x_888_ = l_Std_Time_PlainDate_ofEpochDay(v___x_887_);
lean_dec(v___x_887_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_888_);
v___x_890_ = v___x_883_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_time_881_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_893_, lean_object* v_days_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_Time_PlainDateTime_subDays(v_dt_893_, v_days_894_);
lean_dec(v_days_894_);
return v_res_895_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(7u);
v___x_897_ = lean_nat_to_int(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_898_, lean_object* v_weeks_899_){
_start:
{
lean_object* v_date_900_; lean_object* v_time_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_913_; 
v_date_900_ = lean_ctor_get(v_dt_898_, 0);
v_time_901_ = lean_ctor_get(v_dt_898_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_dt_898_);
if (v_isSharedCheck_913_ == 0)
{
v___x_903_ = v_dt_898_;
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_time_901_);
lean_inc(v_date_900_);
lean_dec(v_dt_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_dateDays_905_; lean_object* v___x_906_; lean_object* v_daysToAdd_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_dateDays_905_ = l_Std_Time_PlainDate_toEpochDay(v_date_900_);
v___x_906_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_907_ = lean_int_mul(v_weeks_899_, v___x_906_);
v___x_908_ = lean_int_add(v_dateDays_905_, v_daysToAdd_907_);
lean_dec(v_daysToAdd_907_);
lean_dec(v_dateDays_905_);
v___x_909_ = l_Std_Time_PlainDate_ofEpochDay(v___x_908_);
lean_dec(v___x_908_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_909_);
v___x_911_ = v___x_903_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_time_901_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_914_, lean_object* v_weeks_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_914_, v_weeks_915_);
lean_dec(v_weeks_915_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_917_, lean_object* v_weeks_918_){
_start:
{
lean_object* v_date_919_; lean_object* v_time_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_933_; 
v_date_919_ = lean_ctor_get(v_dt_917_, 0);
v_time_920_ = lean_ctor_get(v_dt_917_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_dt_917_);
if (v_isSharedCheck_933_ == 0)
{
v___x_922_ = v_dt_917_;
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_time_920_);
lean_inc(v_date_919_);
lean_dec(v_dt_917_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v_dateDays_925_; lean_object* v___x_926_; lean_object* v_daysToAdd_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_924_ = lean_int_neg(v_weeks_918_);
v_dateDays_925_ = l_Std_Time_PlainDate_toEpochDay(v_date_919_);
v___x_926_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_927_ = lean_int_mul(v___x_924_, v___x_926_);
lean_dec(v___x_924_);
v___x_928_ = lean_int_add(v_dateDays_925_, v_daysToAdd_927_);
lean_dec(v_daysToAdd_927_);
lean_dec(v_dateDays_925_);
v___x_929_ = l_Std_Time_PlainDate_ofEpochDay(v___x_928_);
lean_dec(v___x_928_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_929_);
v___x_931_ = v___x_922_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_time_920_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_934_, lean_object* v_weeks_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_934_, v_weeks_935_);
lean_dec(v_weeks_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_937_, lean_object* v_months_938_){
_start:
{
lean_object* v_date_939_; lean_object* v_time_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_date_939_ = lean_ctor_get(v_dt_937_, 0);
v_time_940_ = lean_ctor_get(v_dt_937_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_dt_937_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v_dt_937_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_time_940_);
lean_inc(v_date_939_);
lean_dec(v_dt_937_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = l_Std_Time_PlainDate_addMonthsClip(v_date_939_, v_months_938_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_time_940_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_949_, lean_object* v_months_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_949_, v_months_950_);
lean_dec(v_months_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_952_, lean_object* v_months_953_){
_start:
{
lean_object* v_date_954_; lean_object* v_time_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_964_; 
v_date_954_ = lean_ctor_get(v_dt_952_, 0);
v_time_955_ = lean_ctor_get(v_dt_952_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_dt_952_);
if (v_isSharedCheck_964_ == 0)
{
v___x_957_ = v_dt_952_;
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_time_955_);
lean_inc(v_date_954_);
lean_dec(v_dt_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_959_ = lean_int_neg(v_months_953_);
v___x_960_ = l_Std_Time_PlainDate_addMonthsClip(v_date_954_, v___x_959_);
lean_dec(v___x_959_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_time_955_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_965_, lean_object* v_months_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_965_, v_months_966_);
lean_dec(v_months_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_968_, lean_object* v_months_969_){
_start:
{
lean_object* v_date_970_; lean_object* v_time_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_date_970_ = lean_ctor_get(v_dt_968_, 0);
v_time_971_ = lean_ctor_get(v_dt_968_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_dt_968_);
if (v_isSharedCheck_979_ == 0)
{
v___x_973_ = v_dt_968_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_time_971_);
lean_inc(v_date_970_);
lean_dec(v_dt_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_970_, v_months_969_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_time_971_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_980_, lean_object* v_months_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_980_, v_months_981_);
lean_dec(v_months_981_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_983_, lean_object* v_months_984_){
_start:
{
lean_object* v_date_985_; lean_object* v_time_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_995_; 
v_date_985_ = lean_ctor_get(v_dt_983_, 0);
v_time_986_ = lean_ctor_get(v_dt_983_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_dt_983_);
if (v_isSharedCheck_995_ == 0)
{
v___x_988_ = v_dt_983_;
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_time_986_);
lean_inc(v_date_985_);
lean_dec(v_dt_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = lean_int_neg(v_months_984_);
v___x_991_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_985_, v___x_990_);
lean_dec(v___x_990_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_time_986_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_996_, lean_object* v_months_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_996_, v_months_997_);
lean_dec(v_months_997_);
return v_res_998_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_unsigned_to_nat(12u);
v___x_1000_ = lean_nat_to_int(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_1001_, lean_object* v_years_1002_){
_start:
{
lean_object* v_date_1003_; lean_object* v_time_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1014_; 
v_date_1003_ = lean_ctor_get(v_dt_1001_, 0);
v_time_1004_ = lean_ctor_get(v_dt_1001_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_dt_1001_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1006_ = v_dt_1001_;
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_time_1004_);
lean_inc(v_date_1003_);
lean_dec(v_dt_1001_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1008_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1009_ = lean_int_mul(v_years_1002_, v___x_1008_);
v___x_1010_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1003_, v___x_1009_);
lean_dec(v___x_1009_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1010_);
v___x_1012_ = v___x_1006_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_time_1004_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_1015_, lean_object* v_years_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_1015_, v_years_1016_);
lean_dec(v_years_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_1018_, lean_object* v_years_1019_){
_start:
{
lean_object* v_date_1020_; lean_object* v_time_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1031_; 
v_date_1020_ = lean_ctor_get(v_dt_1018_, 0);
v_time_1021_ = lean_ctor_get(v_dt_1018_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_dt_1018_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1023_ = v_dt_1018_;
v_isShared_1024_ = v_isSharedCheck_1031_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_time_1021_);
lean_inc(v_date_1020_);
lean_dec(v_dt_1018_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1031_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1025_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1026_ = lean_int_mul(v_years_1019_, v___x_1025_);
v___x_1027_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1020_, v___x_1026_);
lean_dec(v___x_1026_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1027_);
v___x_1029_ = v___x_1023_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_time_1021_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_1032_, lean_object* v_years_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_1032_, v_years_1033_);
lean_dec(v_years_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_1035_, lean_object* v_years_1036_){
_start:
{
lean_object* v_date_1037_; lean_object* v_time_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_date_1037_ = lean_ctor_get(v_dt_1035_, 0);
v_time_1038_ = lean_ctor_get(v_dt_1035_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_dt_1035_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v_dt_1035_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_time_1038_);
lean_inc(v_date_1037_);
lean_dec(v_dt_1035_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1042_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1043_ = lean_int_mul(v_years_1036_, v___x_1042_);
v___x_1044_ = lean_int_neg(v___x_1043_);
lean_dec(v___x_1043_);
v___x_1045_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1037_, v___x_1044_);
lean_dec(v___x_1044_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1045_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_time_1038_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_1050_, lean_object* v_years_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_1050_, v_years_1051_);
lean_dec(v_years_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_1053_, lean_object* v_years_1054_){
_start:
{
lean_object* v_date_1055_; lean_object* v_time_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1067_; 
v_date_1055_ = lean_ctor_get(v_dt_1053_, 0);
v_time_1056_ = lean_ctor_get(v_dt_1053_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_dt_1053_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1058_ = v_dt_1053_;
v_isShared_1059_ = v_isSharedCheck_1067_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_time_1056_);
lean_inc(v_date_1055_);
lean_dec(v_dt_1053_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1067_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1060_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1061_ = lean_int_mul(v_years_1054_, v___x_1060_);
v___x_1062_ = lean_int_neg(v___x_1061_);
lean_dec(v___x_1061_);
v___x_1063_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1055_, v___x_1062_);
lean_dec(v___x_1062_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1063_);
v___x_1065_ = v___x_1058_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_time_1056_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_1068_, lean_object* v_years_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_1068_, v_years_1069_);
lean_dec(v_years_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_1071_, lean_object* v_nanos_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v_second_1074_; lean_object* v_nano_1075_; lean_object* v___x_1076_; lean_object* v_second_1077_; lean_object* v_nano_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_nanos_1081_; lean_object* v___x_1082_; lean_object* v_nanos_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1073_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1071_);
v_second_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_second_1074_);
v_nano_1075_ = lean_ctor_get(v___x_1073_, 1);
lean_inc(v_nano_1075_);
lean_dec_ref(v___x_1073_);
v___x_1076_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1072_);
v_second_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_second_1077_);
v_nano_1078_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_nano_1078_);
lean_dec_ref(v___x_1076_);
v___x_1079_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1080_ = lean_int_mul(v_second_1074_, v___x_1079_);
lean_dec(v_second_1074_);
v_nanos_1081_ = lean_int_add(v___x_1080_, v_nano_1075_);
lean_dec(v_nano_1075_);
lean_dec(v___x_1080_);
v___x_1082_ = lean_int_mul(v_second_1077_, v___x_1079_);
lean_dec(v_second_1077_);
v_nanos_1083_ = lean_int_add(v___x_1082_, v_nano_1078_);
lean_dec(v_nano_1078_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_int_add(v_nanos_1081_, v_nanos_1083_);
lean_dec(v_nanos_1083_);
lean_dec(v_nanos_1081_);
v___x_1085_ = l_Std_Time_Duration_ofNanoseconds(v___x_1084_);
lean_dec(v___x_1084_);
v___x_1086_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_1087_, lean_object* v_nanos_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_1087_, v_nanos_1088_);
lean_dec(v_nanos_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_1090_, lean_object* v_nanos_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v_second_1093_; lean_object* v_nano_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_second_1097_; lean_object* v_nano_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_nanos_1101_; lean_object* v___x_1102_; lean_object* v_nanos_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1092_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1090_);
v_second_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_second_1093_);
v_nano_1094_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_nano_1094_);
lean_dec_ref(v___x_1092_);
v___x_1095_ = lean_int_neg(v_nanos_1091_);
v___x_1096_ = l_Std_Time_Duration_ofNanoseconds(v___x_1095_);
lean_dec(v___x_1095_);
v_second_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_second_1097_);
v_nano_1098_ = lean_ctor_get(v___x_1096_, 1);
lean_inc(v_nano_1098_);
lean_dec_ref(v___x_1096_);
v___x_1099_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1100_ = lean_int_mul(v_second_1093_, v___x_1099_);
lean_dec(v_second_1093_);
v_nanos_1101_ = lean_int_add(v___x_1100_, v_nano_1094_);
lean_dec(v_nano_1094_);
lean_dec(v___x_1100_);
v___x_1102_ = lean_int_mul(v_second_1097_, v___x_1099_);
lean_dec(v_second_1097_);
v_nanos_1103_ = lean_int_add(v___x_1102_, v_nano_1098_);
lean_dec(v_nano_1098_);
lean_dec(v___x_1102_);
v___x_1104_ = lean_int_add(v_nanos_1101_, v_nanos_1103_);
lean_dec(v_nanos_1103_);
lean_dec(v_nanos_1101_);
v___x_1105_ = l_Std_Time_Duration_ofNanoseconds(v___x_1104_);
lean_dec(v___x_1104_);
v___x_1106_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_1107_, lean_object* v_nanos_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_1107_, v_nanos_1108_);
lean_dec(v_nanos_1108_);
return v_res_1109_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_cstr_to_nat("3600000000000");
v___x_1111_ = lean_nat_to_int(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_1112_, lean_object* v_hours_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v_second_1115_; lean_object* v_nano_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_second_1120_; lean_object* v_nano_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_nanos_1124_; lean_object* v___x_1125_; lean_object* v_nanos_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1114_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1112_);
v_second_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_second_1115_);
v_nano_1116_ = lean_ctor_get(v___x_1114_, 1);
lean_inc(v_nano_1116_);
lean_dec_ref(v___x_1114_);
v___x_1117_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1118_ = lean_int_mul(v_hours_1113_, v___x_1117_);
v___x_1119_ = l_Std_Time_Duration_ofNanoseconds(v___x_1118_);
lean_dec(v___x_1118_);
v_second_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_second_1120_);
v_nano_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc(v_nano_1121_);
lean_dec_ref(v___x_1119_);
v___x_1122_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1123_ = lean_int_mul(v_second_1115_, v___x_1122_);
lean_dec(v_second_1115_);
v_nanos_1124_ = lean_int_add(v___x_1123_, v_nano_1116_);
lean_dec(v_nano_1116_);
lean_dec(v___x_1123_);
v___x_1125_ = lean_int_mul(v_second_1120_, v___x_1122_);
lean_dec(v_second_1120_);
v_nanos_1126_ = lean_int_add(v___x_1125_, v_nano_1121_);
lean_dec(v_nano_1121_);
lean_dec(v___x_1125_);
v___x_1127_ = lean_int_add(v_nanos_1124_, v_nanos_1126_);
lean_dec(v_nanos_1126_);
lean_dec(v_nanos_1124_);
v___x_1128_ = l_Std_Time_Duration_ofNanoseconds(v___x_1127_);
lean_dec(v___x_1127_);
v___x_1129_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_1130_, lean_object* v_hours_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Std_Time_PlainDateTime_addHours(v_dt_1130_, v_hours_1131_);
lean_dec(v_hours_1131_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_1133_, lean_object* v_hours_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v_second_1136_; lean_object* v_nano_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_second_1142_; lean_object* v_nano_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_nanos_1146_; lean_object* v___x_1147_; lean_object* v_nanos_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1135_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1133_);
v_second_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_second_1136_);
v_nano_1137_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_nano_1137_);
lean_dec_ref(v___x_1135_);
v___x_1138_ = lean_int_neg(v_hours_1134_);
v___x_1139_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1140_ = lean_int_mul(v___x_1138_, v___x_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = l_Std_Time_Duration_ofNanoseconds(v___x_1140_);
lean_dec(v___x_1140_);
v_second_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_second_1142_);
v_nano_1143_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_nano_1143_);
lean_dec_ref(v___x_1141_);
v___x_1144_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1145_ = lean_int_mul(v_second_1136_, v___x_1144_);
lean_dec(v_second_1136_);
v_nanos_1146_ = lean_int_add(v___x_1145_, v_nano_1137_);
lean_dec(v_nano_1137_);
lean_dec(v___x_1145_);
v___x_1147_ = lean_int_mul(v_second_1142_, v___x_1144_);
lean_dec(v_second_1142_);
v_nanos_1148_ = lean_int_add(v___x_1147_, v_nano_1143_);
lean_dec(v_nano_1143_);
lean_dec(v___x_1147_);
v___x_1149_ = lean_int_add(v_nanos_1146_, v_nanos_1148_);
lean_dec(v_nanos_1148_);
lean_dec(v_nanos_1146_);
v___x_1150_ = l_Std_Time_Duration_ofNanoseconds(v___x_1149_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_1152_, lean_object* v_hours_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Std_Time_PlainDateTime_subHours(v_dt_1152_, v_hours_1153_);
lean_dec(v_hours_1153_);
return v_res_1154_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_cstr_to_nat("60000000000");
v___x_1156_ = lean_nat_to_int(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_1157_, lean_object* v_minutes_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v_second_1160_; lean_object* v_nano_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_second_1165_; lean_object* v_nano_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_nanos_1169_; lean_object* v___x_1170_; lean_object* v_nanos_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1159_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1157_);
v_second_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_second_1160_);
v_nano_1161_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_nano_1161_);
lean_dec_ref(v___x_1159_);
v___x_1162_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1163_ = lean_int_mul(v_minutes_1158_, v___x_1162_);
v___x_1164_ = l_Std_Time_Duration_ofNanoseconds(v___x_1163_);
lean_dec(v___x_1163_);
v_second_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_second_1165_);
v_nano_1166_ = lean_ctor_get(v___x_1164_, 1);
lean_inc(v_nano_1166_);
lean_dec_ref(v___x_1164_);
v___x_1167_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1168_ = lean_int_mul(v_second_1160_, v___x_1167_);
lean_dec(v_second_1160_);
v_nanos_1169_ = lean_int_add(v___x_1168_, v_nano_1161_);
lean_dec(v_nano_1161_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_int_mul(v_second_1165_, v___x_1167_);
lean_dec(v_second_1165_);
v_nanos_1171_ = lean_int_add(v___x_1170_, v_nano_1166_);
lean_dec(v_nano_1166_);
lean_dec(v___x_1170_);
v___x_1172_ = lean_int_add(v_nanos_1169_, v_nanos_1171_);
lean_dec(v_nanos_1171_);
lean_dec(v_nanos_1169_);
v___x_1173_ = l_Std_Time_Duration_ofNanoseconds(v___x_1172_);
lean_dec(v___x_1172_);
v___x_1174_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_1175_, lean_object* v_minutes_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_1175_, v_minutes_1176_);
lean_dec(v_minutes_1176_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_1178_, lean_object* v_minutes_1179_){
_start:
{
lean_object* v___x_1180_; lean_object* v_second_1181_; lean_object* v_nano_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_second_1187_; lean_object* v_nano_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_nanos_1191_; lean_object* v___x_1192_; lean_object* v_nanos_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1180_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1178_);
v_second_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_second_1181_);
v_nano_1182_ = lean_ctor_get(v___x_1180_, 1);
lean_inc(v_nano_1182_);
lean_dec_ref(v___x_1180_);
v___x_1183_ = lean_int_neg(v_minutes_1179_);
v___x_1184_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1185_ = lean_int_mul(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = l_Std_Time_Duration_ofNanoseconds(v___x_1185_);
lean_dec(v___x_1185_);
v_second_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_second_1187_);
v_nano_1188_ = lean_ctor_get(v___x_1186_, 1);
lean_inc(v_nano_1188_);
lean_dec_ref(v___x_1186_);
v___x_1189_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1190_ = lean_int_mul(v_second_1181_, v___x_1189_);
lean_dec(v_second_1181_);
v_nanos_1191_ = lean_int_add(v___x_1190_, v_nano_1182_);
lean_dec(v_nano_1182_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_int_mul(v_second_1187_, v___x_1189_);
lean_dec(v_second_1187_);
v_nanos_1193_ = lean_int_add(v___x_1192_, v_nano_1188_);
lean_dec(v_nano_1188_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_int_add(v_nanos_1191_, v_nanos_1193_);
lean_dec(v_nanos_1193_);
lean_dec(v_nanos_1191_);
v___x_1195_ = l_Std_Time_Duration_ofNanoseconds(v___x_1194_);
lean_dec(v___x_1194_);
v___x_1196_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_1197_, lean_object* v_minutes_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_1197_, v_minutes_1198_);
lean_dec(v_minutes_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_1200_, lean_object* v_seconds_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v_second_1203_; lean_object* v_nano_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_second_1208_; lean_object* v_nano_1209_; lean_object* v___x_1210_; lean_object* v_nanos_1211_; lean_object* v___x_1212_; lean_object* v_nanos_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1202_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1200_);
v_second_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_second_1203_);
v_nano_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_nano_1204_);
lean_dec_ref(v___x_1202_);
v___x_1205_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1206_ = lean_int_mul(v_seconds_1201_, v___x_1205_);
v___x_1207_ = l_Std_Time_Duration_ofNanoseconds(v___x_1206_);
lean_dec(v___x_1206_);
v_second_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_second_1208_);
v_nano_1209_ = lean_ctor_get(v___x_1207_, 1);
lean_inc(v_nano_1209_);
lean_dec_ref(v___x_1207_);
v___x_1210_ = lean_int_mul(v_second_1203_, v___x_1205_);
lean_dec(v_second_1203_);
v_nanos_1211_ = lean_int_add(v___x_1210_, v_nano_1204_);
lean_dec(v_nano_1204_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_int_mul(v_second_1208_, v___x_1205_);
lean_dec(v_second_1208_);
v_nanos_1213_ = lean_int_add(v___x_1212_, v_nano_1209_);
lean_dec(v_nano_1209_);
lean_dec(v___x_1212_);
v___x_1214_ = lean_int_add(v_nanos_1211_, v_nanos_1213_);
lean_dec(v_nanos_1213_);
lean_dec(v_nanos_1211_);
v___x_1215_ = l_Std_Time_Duration_ofNanoseconds(v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_1217_, lean_object* v_seconds_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_1217_, v_seconds_1218_);
lean_dec(v_seconds_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_1220_, lean_object* v_seconds_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v_second_1223_; lean_object* v_nano_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_second_1229_; lean_object* v_nano_1230_; lean_object* v___x_1231_; lean_object* v_nanos_1232_; lean_object* v___x_1233_; lean_object* v_nanos_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1222_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1220_);
v_second_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_second_1223_);
v_nano_1224_ = lean_ctor_get(v___x_1222_, 1);
lean_inc(v_nano_1224_);
lean_dec_ref(v___x_1222_);
v___x_1225_ = lean_int_neg(v_seconds_1221_);
v___x_1226_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1227_ = lean_int_mul(v___x_1225_, v___x_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = l_Std_Time_Duration_ofNanoseconds(v___x_1227_);
lean_dec(v___x_1227_);
v_second_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_second_1229_);
v_nano_1230_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_nano_1230_);
lean_dec_ref(v___x_1228_);
v___x_1231_ = lean_int_mul(v_second_1223_, v___x_1226_);
lean_dec(v_second_1223_);
v_nanos_1232_ = lean_int_add(v___x_1231_, v_nano_1224_);
lean_dec(v_nano_1224_);
lean_dec(v___x_1231_);
v___x_1233_ = lean_int_mul(v_second_1229_, v___x_1226_);
lean_dec(v_second_1229_);
v_nanos_1234_ = lean_int_add(v___x_1233_, v_nano_1230_);
lean_dec(v_nano_1230_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_int_add(v_nanos_1232_, v_nanos_1234_);
lean_dec(v_nanos_1234_);
lean_dec(v_nanos_1232_);
v___x_1236_ = l_Std_Time_Duration_ofNanoseconds(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1237_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_1238_, lean_object* v_seconds_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_1238_, v_seconds_1239_);
lean_dec(v_seconds_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_1241_, lean_object* v_milliseconds_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v_second_1244_; lean_object* v_nano_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_second_1249_; lean_object* v_nano_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_nanos_1253_; lean_object* v___x_1254_; lean_object* v_nanos_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1243_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1241_);
v_second_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_second_1244_);
v_nano_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_nano_1245_);
lean_dec_ref(v___x_1243_);
v___x_1246_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1247_ = lean_int_mul(v_milliseconds_1242_, v___x_1246_);
v___x_1248_ = l_Std_Time_Duration_ofNanoseconds(v___x_1247_);
lean_dec(v___x_1247_);
v_second_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_second_1249_);
v_nano_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_nano_1250_);
lean_dec_ref(v___x_1248_);
v___x_1251_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1252_ = lean_int_mul(v_second_1244_, v___x_1251_);
lean_dec(v_second_1244_);
v_nanos_1253_ = lean_int_add(v___x_1252_, v_nano_1245_);
lean_dec(v_nano_1245_);
lean_dec(v___x_1252_);
v___x_1254_ = lean_int_mul(v_second_1249_, v___x_1251_);
lean_dec(v_second_1249_);
v_nanos_1255_ = lean_int_add(v___x_1254_, v_nano_1250_);
lean_dec(v_nano_1250_);
lean_dec(v___x_1254_);
v___x_1256_ = lean_int_add(v_nanos_1253_, v_nanos_1255_);
lean_dec(v_nanos_1255_);
lean_dec(v_nanos_1253_);
v___x_1257_ = l_Std_Time_Duration_ofNanoseconds(v___x_1256_);
lean_dec(v___x_1256_);
v___x_1258_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_1259_, lean_object* v_milliseconds_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_1259_, v_milliseconds_1260_);
lean_dec(v_milliseconds_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_1262_, lean_object* v_milliseconds_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v_second_1265_; lean_object* v_nano_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_second_1271_; lean_object* v_nano_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_nanos_1275_; lean_object* v___x_1276_; lean_object* v_nanos_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1264_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1262_);
v_second_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_second_1265_);
v_nano_1266_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_nano_1266_);
lean_dec_ref(v___x_1264_);
v___x_1267_ = lean_int_neg(v_milliseconds_1263_);
v___x_1268_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1269_ = lean_int_mul(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = l_Std_Time_Duration_ofNanoseconds(v___x_1269_);
lean_dec(v___x_1269_);
v_second_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_second_1271_);
v_nano_1272_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_nano_1272_);
lean_dec_ref(v___x_1270_);
v___x_1273_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1274_ = lean_int_mul(v_second_1265_, v___x_1273_);
lean_dec(v_second_1265_);
v_nanos_1275_ = lean_int_add(v___x_1274_, v_nano_1266_);
lean_dec(v_nano_1266_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_int_mul(v_second_1271_, v___x_1273_);
lean_dec(v_second_1271_);
v_nanos_1277_ = lean_int_add(v___x_1276_, v_nano_1272_);
lean_dec(v_nano_1272_);
lean_dec(v___x_1276_);
v___x_1278_ = lean_int_add(v_nanos_1275_, v_nanos_1277_);
lean_dec(v_nanos_1277_);
lean_dec(v_nanos_1275_);
v___x_1279_ = l_Std_Time_Duration_ofNanoseconds(v___x_1278_);
lean_dec(v___x_1278_);
v___x_1280_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1281_, lean_object* v_milliseconds_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1281_, v_milliseconds_1282_);
lean_dec(v_milliseconds_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1284_){
_start:
{
lean_object* v_date_1285_; lean_object* v_year_1286_; 
v_date_1285_ = lean_ctor_get(v_dt_1284_, 0);
v_year_1286_ = lean_ctor_get(v_date_1285_, 0);
lean_inc(v_year_1286_);
return v_year_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_Time_PlainDateTime_year(v_dt_1287_);
lean_dec_ref(v_dt_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1289_){
_start:
{
lean_object* v_date_1290_; lean_object* v_month_1291_; 
v_date_1290_ = lean_ctor_get(v_dt_1289_, 0);
v_month_1291_ = lean_ctor_get(v_date_1290_, 1);
lean_inc(v_month_1291_);
return v_month_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_Time_PlainDateTime_month(v_dt_1292_);
lean_dec_ref(v_dt_1292_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1294_){
_start:
{
lean_object* v_date_1295_; lean_object* v_day_1296_; 
v_date_1295_ = lean_ctor_get(v_dt_1294_, 0);
v_day_1296_ = lean_ctor_get(v_date_1295_, 2);
lean_inc(v_day_1296_);
return v_day_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_Time_PlainDateTime_day(v_dt_1297_);
lean_dec_ref(v_dt_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1299_){
_start:
{
lean_object* v_date_1300_; uint8_t v___x_1301_; 
v_date_1300_ = lean_ctor_get(v_dt_1299_, 0);
lean_inc_ref(v_date_1300_);
lean_dec_ref(v_dt_1299_);
v___x_1301_ = l_Std_Time_PlainDate_weekday(v_date_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_Std_Time_PlainDateTime_weekday(v_dt_1302_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1305_){
_start:
{
lean_object* v_time_1306_; lean_object* v_hour_1307_; 
v_time_1306_ = lean_ctor_get(v_dt_1305_, 1);
v_hour_1307_ = lean_ctor_get(v_time_1306_, 0);
lean_inc(v_hour_1307_);
return v_hour_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_Time_PlainDateTime_hour(v_dt_1308_);
lean_dec_ref(v_dt_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1310_){
_start:
{
lean_object* v_time_1311_; lean_object* v_minute_1312_; 
v_time_1311_ = lean_ctor_get(v_dt_1310_, 1);
v_minute_1312_ = lean_ctor_get(v_time_1311_, 1);
lean_inc(v_minute_1312_);
return v_minute_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_Time_PlainDateTime_minute(v_dt_1313_);
lean_dec_ref(v_dt_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1315_){
_start:
{
lean_object* v_time_1316_; lean_object* v_nanosecond_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_time_1316_ = lean_ctor_get(v_dt_1315_, 1);
v_nanosecond_1317_ = lean_ctor_get(v_time_1316_, 3);
v___x_1318_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1319_ = lean_int_ediv(v_nanosecond_1317_, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1320_);
lean_dec_ref(v_dt_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1322_){
_start:
{
lean_object* v_time_1323_; lean_object* v_second_1324_; 
v_time_1323_ = lean_ctor_get(v_dt_1322_, 1);
v_second_1324_ = lean_ctor_get(v_time_1323_, 2);
lean_inc(v_second_1324_);
return v_second_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_Time_PlainDateTime_second(v_dt_1325_);
lean_dec_ref(v_dt_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1327_){
_start:
{
lean_object* v_time_1328_; lean_object* v_nanosecond_1329_; 
v_time_1328_ = lean_ctor_get(v_dt_1327_, 1);
v_nanosecond_1329_ = lean_ctor_get(v_time_1328_, 3);
lean_inc(v_nanosecond_1329_);
return v_nanosecond_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1330_);
lean_dec_ref(v_dt_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1332_){
_start:
{
lean_object* v_date_1333_; lean_object* v_year_1334_; uint8_t v___x_1335_; 
v_date_1333_ = lean_ctor_get(v_date_1332_, 0);
v_year_1334_ = lean_ctor_get(v_date_1333_, 0);
v___x_1335_ = l_Std_Time_Year_Offset_era(v_year_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1336_){
_start:
{
uint8_t v_res_1337_; lean_object* v_r_1338_; 
v_res_1337_ = l_Std_Time_PlainDateTime_era(v_date_1336_);
lean_dec_ref(v_date_1336_);
v_r_1338_ = lean_box(v_res_1337_);
return v_r_1338_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1339_){
_start:
{
lean_object* v_date_1340_; lean_object* v_year_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1349_; 
v_date_1340_ = lean_ctor_get(v_date_1339_, 0);
v_year_1341_ = lean_ctor_get(v_date_1340_, 0);
v___x_1342_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1343_ = lean_int_mod(v_year_1341_, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1349_ = lean_int_dec_eq(v___x_1343_, v___x_1344_);
lean_dec(v___x_1343_);
if (v___x_1349_ == 0)
{
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1351_ = lean_int_mod(v_year_1341_, v___x_1350_);
v___x_1352_ = lean_int_dec_eq(v___x_1351_, v___x_1344_);
lean_dec(v___x_1351_);
if (v___x_1352_ == 0)
{
if (v___x_1349_ == 0)
{
goto v___jp_1345_;
}
else
{
return v___x_1349_;
}
}
else
{
goto v___jp_1345_;
}
}
v___jp_1345_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1347_ = lean_int_mod(v_year_1341_, v___x_1346_);
v___x_1348_ = lean_int_dec_eq(v___x_1347_, v___x_1344_);
lean_dec(v___x_1347_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object* v_date_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1353_);
lean_dec_ref(v_date_1353_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1356_, uint8_t v_firstDay_1357_, lean_object* v_minDays_1358_){
_start:
{
lean_object* v_date_1359_; lean_object* v___x_1360_; 
v_date_1359_ = lean_ctor_get(v_date_1356_, 0);
lean_inc_ref(v_date_1359_);
lean_dec_ref(v_date_1356_);
v___x_1360_ = l_Std_Time_PlainDate_weekOfYear(v_date_1359_, v_firstDay_1357_, v_minDays_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear___boxed(lean_object* v_date_1361_, lean_object* v_firstDay_1362_, lean_object* v_minDays_1363_){
_start:
{
uint8_t v_firstDay_boxed_1364_; lean_object* v_res_1365_; 
v_firstDay_boxed_1364_ = lean_unbox(v_firstDay_1362_);
v_res_1365_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_1361_, v_firstDay_boxed_1364_, v_minDays_1363_);
lean_dec(v_minDays_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object* v_date_1366_, uint8_t v_firstDay_1367_, lean_object* v_minDays_1368_){
_start:
{
lean_object* v_date_1369_; lean_object* v___x_1370_; 
v_date_1369_ = lean_ctor_get(v_date_1366_, 0);
lean_inc_ref(v_date_1369_);
lean_dec_ref(v_date_1366_);
v___x_1370_ = l_Std_Time_PlainDate_weekYear(v_date_1369_, v_firstDay_1367_, v_minDays_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object* v_date_1371_, lean_object* v_firstDay_1372_, lean_object* v_minDays_1373_){
_start:
{
uint8_t v_firstDay_boxed_1374_; lean_object* v_res_1375_; 
v_firstDay_boxed_1374_ = lean_unbox(v_firstDay_1372_);
v_res_1375_ = l_Std_Time_PlainDateTime_weekYear(v_date_1371_, v_firstDay_boxed_1374_, v_minDays_1373_);
lean_dec(v_minDays_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1376_){
_start:
{
lean_object* v_date_1377_; lean_object* v___x_1378_; 
v_date_1377_ = lean_ctor_get(v_date_1376_, 0);
v___x_1378_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1379_);
lean_dec_ref(v_date_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1381_, uint8_t v_firstDay_1382_){
_start:
{
lean_object* v_date_1383_; lean_object* v___x_1384_; 
v_date_1383_ = lean_ctor_get(v_date_1381_, 0);
lean_inc_ref(v_date_1383_);
lean_dec_ref(v_date_1381_);
v___x_1384_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1383_, v_firstDay_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1385_, lean_object* v_firstDay_1386_){
_start:
{
uint8_t v_firstDay_boxed_1387_; lean_object* v_res_1388_; 
v_firstDay_boxed_1387_ = lean_unbox(v_firstDay_1386_);
v_res_1388_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1385_, v_firstDay_boxed_1387_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1389_){
_start:
{
lean_object* v_date_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1414_; 
v_date_1390_ = lean_ctor_get(v_date_1389_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_date_1389_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_date_1389_, 1);
lean_dec(v_unused_1415_);
v___x_1392_ = v_date_1389_;
v_isShared_1393_ = v_isSharedCheck_1414_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_date_1390_);
lean_dec(v_date_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1414_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_year_1394_; lean_object* v_month_1395_; lean_object* v_day_1396_; uint8_t v___y_1398_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1410_; 
v_year_1394_ = lean_ctor_get(v_date_1390_, 0);
lean_inc(v_year_1394_);
v_month_1395_ = lean_ctor_get(v_date_1390_, 1);
lean_inc(v_month_1395_);
v_day_1396_ = lean_ctor_get(v_date_1390_, 2);
lean_inc(v_day_1396_);
lean_dec_ref(v_date_1390_);
v___x_1403_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1404_ = lean_int_mod(v_year_1394_, v___x_1403_);
v___x_1405_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1410_ = lean_int_dec_eq(v___x_1404_, v___x_1405_);
lean_dec(v___x_1404_);
if (v___x_1410_ == 0)
{
lean_dec(v_year_1394_);
v___y_1398_ = v___x_1410_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1412_ = lean_int_mod(v_year_1394_, v___x_1411_);
v___x_1413_ = lean_int_dec_eq(v___x_1412_, v___x_1405_);
lean_dec(v___x_1412_);
if (v___x_1413_ == 0)
{
if (v___x_1410_ == 0)
{
goto v___jp_1406_;
}
else
{
lean_dec(v_year_1394_);
v___y_1398_ = v___x_1410_;
goto v___jp_1397_;
}
}
else
{
goto v___jp_1406_;
}
}
v___jp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v_day_1396_);
lean_ctor_set(v___x_1392_, 0, v_month_1395_);
v___x_1400_ = v___x_1392_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_month_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_day_1396_);
v___x_1400_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Std_Time_ValidDate_dayOfYear(v___y_1398_, v___x_1400_);
lean_dec_ref(v___x_1400_);
return v___x_1401_;
}
}
v___jp_1406_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1408_ = lean_int_mod(v_year_1394_, v___x_1407_);
lean_dec(v_year_1394_);
v___x_1409_ = lean_int_dec_eq(v___x_1408_, v___x_1405_);
lean_dec(v___x_1408_);
v___y_1398_ = v___x_1409_;
goto v___jp_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object* v_date_1416_){
_start:
{
lean_object* v_date_1417_; lean_object* v___x_1418_; 
v_date_1417_ = lean_ctor_get(v_date_1416_, 0);
v___x_1418_ = l_Std_Time_PlainDate_quarter(v_date_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object* v_date_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_Time_PlainDateTime_quarter(v_date_1419_);
lean_dec_ref(v_date_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object* v_date_1421_, lean_object* v_time_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_date_1421_);
lean_ctor_set(v___x_1423_, 1, v_time_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object* v_time_1424_, lean_object* v_date_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_date_1425_);
lean_ctor_set(v___x_1426_, 1, v_time_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object* v_x_1455_, lean_object* v_y_1456_){
_start:
{
lean_object* v_second_1457_; lean_object* v_nano_1458_; lean_object* v___x_1459_; lean_object* v_second_1460_; lean_object* v_nano_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_nanos_1464_; lean_object* v___x_1465_; lean_object* v_second_1466_; lean_object* v_nano_1467_; lean_object* v___x_1468_; lean_object* v_nanos_1469_; lean_object* v___x_1470_; lean_object* v_nanos_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_second_1457_ = lean_ctor_get(v_y_1456_, 0);
v_nano_1458_ = lean_ctor_get(v_y_1456_, 1);
v___x_1459_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1455_);
v_second_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_second_1460_);
v_nano_1461_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_nano_1461_);
lean_dec_ref(v___x_1459_);
v___x_1462_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1463_ = lean_int_mul(v_second_1457_, v___x_1462_);
v_nanos_1464_ = lean_int_add(v___x_1463_, v_nano_1458_);
lean_dec(v___x_1463_);
v___x_1465_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1464_);
lean_dec(v_nanos_1464_);
v_second_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_second_1466_);
v_nano_1467_ = lean_ctor_get(v___x_1465_, 1);
lean_inc(v_nano_1467_);
lean_dec_ref(v___x_1465_);
v___x_1468_ = lean_int_mul(v_second_1460_, v___x_1462_);
lean_dec(v_second_1460_);
v_nanos_1469_ = lean_int_add(v___x_1468_, v_nano_1461_);
lean_dec(v_nano_1461_);
lean_dec(v___x_1468_);
v___x_1470_ = lean_int_mul(v_second_1466_, v___x_1462_);
lean_dec(v_second_1466_);
v_nanos_1471_ = lean_int_add(v___x_1470_, v_nano_1467_);
lean_dec(v_nano_1467_);
lean_dec(v___x_1470_);
v___x_1472_ = lean_int_add(v_nanos_1469_, v_nanos_1471_);
lean_dec(v_nanos_1471_);
lean_dec(v_nanos_1469_);
v___x_1473_ = l_Std_Time_Duration_ofNanoseconds(v___x_1472_);
lean_dec(v___x_1472_);
v___x_1474_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1475_, lean_object* v_y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_1475_, v_y_1476_);
lean_dec_ref(v_y_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = l_Std_Time_PlainTime_midnight;
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_date_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_1483_){
_start:
{
lean_object* v_date_1484_; 
v_date_1484_ = lean_ctor_get(v_pdt_1483_, 0);
lean_inc_ref(v_date_1484_);
return v_date_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_1485_);
lean_dec_ref(v_pdt_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_1487_){
_start:
{
lean_object* v_time_1488_; 
v_time_1488_ = lean_ctor_get(v_pdt_1487_, 1);
lean_inc_ref(v_time_1488_);
return v_time_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_1489_);
lean_dec_ref(v_pdt_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_1491_, lean_object* v_y_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v_second_1494_; lean_object* v_nano_1495_; lean_object* v___x_1496_; lean_object* v_second_1497_; lean_object* v_nano_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_nanos_1503_; lean_object* v___x_1504_; lean_object* v_nanos_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1493_ = l_Std_Time_PlainDateTime_toWallTime(v_y_1492_);
v_second_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_second_1494_);
v_nano_1495_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_nano_1495_);
lean_dec_ref(v___x_1493_);
v___x_1496_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1491_);
v_second_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_second_1497_);
v_nano_1498_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_nano_1498_);
lean_dec_ref(v___x_1496_);
v___x_1499_ = lean_int_neg(v_second_1494_);
lean_dec(v_second_1494_);
v___x_1500_ = lean_int_neg(v_nano_1495_);
lean_dec(v_nano_1495_);
v___x_1501_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1502_ = lean_int_mul(v_second_1497_, v___x_1501_);
lean_dec(v_second_1497_);
v_nanos_1503_ = lean_int_add(v___x_1502_, v_nano_1498_);
lean_dec(v_nano_1498_);
lean_dec(v___x_1502_);
v___x_1504_ = lean_int_mul(v___x_1499_, v___x_1501_);
lean_dec(v___x_1499_);
v_nanos_1505_ = lean_int_add(v___x_1504_, v___x_1500_);
lean_dec(v___x_1500_);
lean_dec(v___x_1504_);
v___x_1506_ = lean_int_add(v_nanos_1503_, v_nanos_1505_);
lean_dec(v_nanos_1505_);
lean_dec(v_nanos_1503_);
v___x_1507_ = l_Std_Time_Duration_ofNanoseconds(v___x_1506_);
lean_dec(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object* v_pd_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1511_ = l_Std_Time_PlainDate_toEpochDay(v_pd_1510_);
v___x_1512_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1513_ = lean_int_mul(v___x_1511_, v___x_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object* v_wt_1516_){
_start:
{
lean_object* v_second_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_second_1517_ = lean_ctor_get(v_wt_1516_, 0);
v___x_1518_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1519_ = lean_int_div(v_second_1517_, v___x_1518_);
v___x_1520_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1519_);
lean_dec(v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object* v_wt_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_Time_PlainDate_ofWallTime(v_wt_1521_);
lean_dec_ref(v_wt_1521_);
return v_res_1522_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1524_ = lean_int_neg(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_1525_, lean_object* v_y_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_nanos_1537_; lean_object* v___x_1538_; lean_object* v_nanos_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1527_ = l_Std_Time_PlainDate_toEpochDay(v_x_1525_);
v___x_1528_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1529_ = lean_int_mul(v___x_1527_, v___x_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1531_ = l_Std_Time_PlainDate_toEpochDay(v_y_1526_);
v___x_1532_ = lean_int_mul(v___x_1531_, v___x_1528_);
lean_dec(v___x_1531_);
v___x_1533_ = lean_int_neg(v___x_1532_);
lean_dec(v___x_1532_);
v___x_1534_ = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
v___x_1535_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1536_ = lean_int_mul(v___x_1529_, v___x_1535_);
lean_dec(v___x_1529_);
v_nanos_1537_ = lean_int_add(v___x_1536_, v___x_1530_);
lean_dec(v___x_1536_);
v___x_1538_ = lean_int_mul(v___x_1533_, v___x_1535_);
lean_dec(v___x_1533_);
v_nanos_1539_ = lean_int_add(v___x_1538_, v___x_1534_);
lean_dec(v___x_1538_);
v___x_1540_ = lean_int_add(v_nanos_1537_, v_nanos_1539_);
lean_dec(v_nanos_1539_);
lean_dec(v_nanos_1537_);
v___x_1541_ = l_Std_Time_Duration_ofNanoseconds(v___x_1540_);
lean_dec(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object* v_date_1544_, lean_object* v_time_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_date_1544_);
lean_ctor_set(v___x_1546_, 1, v_time_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object* v_pt_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1547_);
v___x_1549_ = l_Std_Time_Duration_ofNanoseconds(v___x_1548_);
lean_dec(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object* v_pt_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_Time_PlainTime_toWallTime(v_pt_1550_);
lean_dec_ref(v_pt_1550_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object* v_wt_1552_){
_start:
{
lean_object* v_second_1553_; lean_object* v_nano_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_nanos_1557_; lean_object* v___x_1558_; 
v_second_1553_ = lean_ctor_get(v_wt_1552_, 0);
v_nano_1554_ = lean_ctor_get(v_wt_1552_, 1);
v___x_1555_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1556_ = lean_int_mul(v_second_1553_, v___x_1555_);
v_nanos_1557_ = lean_int_add(v___x_1556_, v_nano_1554_);
lean_dec(v___x_1556_);
v___x_1558_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1557_);
lean_dec(v_nanos_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object* v_wt_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_Time_PlainTime_ofWallTime(v_wt_1559_);
lean_dec_ref(v_wt_1559_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object* v_time_1561_, lean_object* v_date_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_date_1562_);
lean_ctor_set(v___x_1563_, 1, v_time_1561_);
return v___x_1563_;
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
