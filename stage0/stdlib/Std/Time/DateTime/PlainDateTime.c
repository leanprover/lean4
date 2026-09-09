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
static lean_once_cell_t l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0;
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
static lean_once_cell_t l_Std_Time_PlainDateTime_ofWallTime___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofWallTime___closed__32;
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
static lean_object* _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(13u);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_mod(v___x_255_, v___x_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(lean_object* v_as_x27_257_, lean_object* v_b_258_){
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
v___x_267_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___boxed(lean_object* v_as_x27_279_, lean_object* v_b_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_279_, v_b_280_);
lean_dec(v_as_x27_279_);
return v_res_281_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(11017u);
v___x_283_ = lean_nat_to_int(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(365u);
v___x_285_ = lean_nat_to_int(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(400u);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_289_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_290_ = lean_int_mul(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(97u);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_daysPer400Y_295_; 
v___x_293_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__4, &l_Std_Time_PlainDateTime_ofWallTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4);
v___x_294_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__3, &l_Std_Time_PlainDateTime_ofWallTime___closed__3_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3);
v_daysPer400Y_295_ = lean_int_add(v___x_294_, v___x_293_);
return v_daysPer400Y_295_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(100u);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_299_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_300_ = lean_int_mul(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(24u);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_daysPer100Y_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__8, &l_Std_Time_PlainDateTime_ofWallTime___closed__8_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8);
v___x_304_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__7, &l_Std_Time_PlainDateTime_ofWallTime___closed__7_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7);
v_daysPer100Y_305_ = lean_int_add(v___x_304_, v___x_303_);
return v_daysPer100Y_305_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_to_int(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_309_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_310_ = lean_int_mul(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_daysPer4Y_313_; 
v___x_311_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_312_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__11, &l_Std_Time_PlainDateTime_ofWallTime___closed__11_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11);
v_daysPer4Y_313_ = lean_int_add(v___x_312_, v___x_311_);
return v_daysPer4Y_313_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(60u);
v___x_315_ = lean_nat_to_int(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(3600u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(31u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(29u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
v___x_323_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__16, &l_Std_Time_PlainDateTime_ofWallTime___closed__16_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__17, &l_Std_Time_PlainDateTime_ofWallTime___closed__17_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17);
v___x_326_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__18, &l_Std_Time_PlainDateTime_ofWallTime___closed__18_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18);
v___x_329_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__19, &l_Std_Time_PlainDateTime_ofWallTime___closed__19_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19);
v___x_332_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__20, &l_Std_Time_PlainDateTime_ofWallTime___closed__20_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20);
v___x_335_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__21, &l_Std_Time_PlainDateTime_ofWallTime___closed__21_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21);
v___x_338_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__22, &l_Std_Time_PlainDateTime_ofWallTime___closed__22_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22);
v___x_341_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__23, &l_Std_Time_PlainDateTime_ofWallTime___closed__23_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23);
v___x_344_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__24, &l_Std_Time_PlainDateTime_ofWallTime___closed__24_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24);
v___x_347_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__25, &l_Std_Time_PlainDateTime_ofWallTime___closed__25_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25);
v___x_350_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__26, &l_Std_Time_PlainDateTime_ofWallTime___closed__26_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26);
v___x_353_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__11, &l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_months_357_; 
v___x_355_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__27, &l_Std_Time_PlainDateTime_ofWallTime___closed__27_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27);
v___x_356_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__15, &l_Std_Time_PlainDateTime_ofWallTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15);
v_months_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_months_357_, 0, v___x_356_);
lean_ctor_set(v_months_357_, 1, v___x_355_);
return v_months_357_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_mon_360_; 
v___x_358_ = lean_unsigned_to_nat(13u);
v___x_359_ = lean_unsigned_to_nat(0u);
v_mon_360_ = lean_nat_mod(v___x_359_, v___x_358_);
return v_mon_360_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(2000u);
v___x_362_ = lean_nat_to_int(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(25u);
v___x_364_ = lean_nat_to_int(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofWallTime___closed__32(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v___x_366_ = lean_int_neg(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object* v_stamp_367_){
_start:
{
lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v___y_390_; uint8_t v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v_second_399_; lean_object* v_nano_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_540_; 
v_second_399_ = lean_ctor_get(v_stamp_367_, 0);
v_nano_400_ = lean_ctor_get(v_stamp_367_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_stamp_367_);
if (v_isSharedCheck_540_ == 0)
{
v___x_402_ = v_stamp_367_;
v_isShared_403_ = v_isSharedCheck_540_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_nano_400_);
lean_inc(v_second_399_);
lean_dec(v_stamp_367_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_540_;
goto v_resetjp_401_;
}
v___jp_368_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_374_, 0, v___y_370_);
lean_ctor_set(v___x_374_, 1, v___y_371_);
lean_ctor_set(v___x_374_, 2, v___y_372_);
lean_ctor_set(v___x_374_, 3, v___y_369_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___y_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
v___jp_376_:
{
lean_object* v_max_385_; uint8_t v___x_386_; 
v_max_385_ = l_Std_Time_Month_Ordinal_days(v___y_384_, v___y_382_);
v___x_386_ = lean_int_dec_lt(v_max_385_, v___y_380_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_max_385_);
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v___y_377_);
lean_ctor_set(v___x_387_, 1, v___y_382_);
lean_ctor_set(v___x_387_, 2, v___y_380_);
v___y_369_ = v___y_378_;
v___y_370_ = v___y_379_;
v___y_371_ = v___y_381_;
v___y_372_ = v___y_383_;
v___y_373_ = v___x_387_;
goto v___jp_368_;
}
else
{
lean_object* v___x_388_; 
lean_dec(v___y_380_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___y_377_);
lean_ctor_set(v___x_388_, 1, v___y_382_);
lean_ctor_set(v___x_388_, 2, v_max_385_);
v___y_369_ = v___y_378_;
v___y_370_ = v___y_379_;
v___y_371_ = v___y_381_;
v___y_372_ = v___y_383_;
v___y_373_ = v___x_388_;
goto v___jp_368_;
}
}
v___jp_389_:
{
if (v___y_391_ == 0)
{
v___y_377_ = v___y_390_;
v___y_378_ = v___y_392_;
v___y_379_ = v___y_393_;
v___y_380_ = v___y_394_;
v___y_381_ = v___y_396_;
v___y_382_ = v___y_395_;
v___y_383_ = v___y_397_;
v___y_384_ = v___y_391_;
goto v___jp_376_;
}
else
{
v___y_377_ = v___y_390_;
v___y_378_ = v___y_392_;
v___y_379_ = v___y_393_;
v___y_380_ = v___y_394_;
v___y_381_ = v___y_396_;
v___y_382_ = v___y_395_;
v___y_383_ = v___y_397_;
v___y_384_ = v___y_398_;
goto v___jp_376_;
}
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_daysPer400Y_407_; lean_object* v___x_408_; lean_object* v_daysPer100Y_409_; lean_object* v___x_410_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_daysPer4Y_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v_hmon_438_; lean_object* v_year_439_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v_remYears_456_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v_quadrennialCycles_492_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v_centenialCycles_502_; lean_object* v___y_510_; lean_object* v_quadracentennialCycles_511_; lean_object* v_remDays_512_; lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v_snd_526_; lean_object* v_secs_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_404_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__0, &l_Std_Time_PlainDateTime_ofWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0);
v___x_405_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__1, &l_Std_Time_PlainDateTime_ofWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1);
v___x_406_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v_daysPer400Y_407_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__5, &l_Std_Time_PlainDateTime_ofWallTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5);
v___x_408_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v_daysPer100Y_409_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__9, &l_Std_Time_PlainDateTime_ofWallTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9);
v___x_410_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__1, &l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1);
v_daysPer4Y_430_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__12, &l_Std_Time_PlainDateTime_ofWallTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12);
v___x_431_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_432_ = lean_int_mul(v_second_399_, v___x_431_);
lean_dec(v_second_399_);
v___x_433_ = lean_int_add(v___x_432_, v_nano_400_);
lean_dec(v_nano_400_);
lean_dec(v___x_432_);
v_secs_535_ = lean_int_div(v___x_433_, v___x_431_);
v___x_536_ = lean_int_mod(v___x_433_, v___x_431_);
v___x_537_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_538_ = lean_int_dec_lt(v___x_536_, v___x_537_);
lean_dec(v___x_536_);
if (v___x_538_ == 0)
{
v_snd_526_ = v_secs_535_;
goto v___jp_525_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_int_sub(v_secs_535_, v___x_429_);
lean_dec(v_secs_535_);
v_snd_526_ = v___x_539_;
goto v___jp_525_;
}
v___jp_411_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_420_ = lean_int_mod(v___y_412_, v___x_410_);
v___x_421_ = lean_nat_to_int(v___y_417_);
v___x_422_ = lean_int_dec_eq(v___x_420_, v___x_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_int_mod(v___y_412_, v___x_408_);
v___x_424_ = lean_int_dec_eq(v___x_423_, v___x_421_);
lean_dec(v___x_423_);
if (v___x_424_ == 0)
{
uint8_t v___x_425_; 
lean_dec(v___x_421_);
v___x_425_ = 1;
v___y_390_ = v___y_412_;
v___y_391_ = v___x_422_;
v___y_392_ = v___y_413_;
v___y_393_ = v___y_414_;
v___y_394_ = v___y_419_;
v___y_395_ = v___y_415_;
v___y_396_ = v___y_416_;
v___y_397_ = v___y_418_;
v___y_398_ = v___x_425_;
goto v___jp_389_;
}
else
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_int_mod(v___y_412_, v___x_406_);
v___x_427_ = lean_int_dec_eq(v___x_426_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v___x_426_);
v___y_390_ = v___y_412_;
v___y_391_ = v___x_422_;
v___y_392_ = v___y_413_;
v___y_393_ = v___y_414_;
v___y_394_ = v___y_419_;
v___y_395_ = v___y_415_;
v___y_396_ = v___y_416_;
v___y_397_ = v___y_418_;
v___y_398_ = v___x_427_;
goto v___jp_389_;
}
}
v___jp_434_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_440_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__13, &l_Std_Time_PlainDateTime_ofWallTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13);
v___x_441_ = lean_int_emod(v___y_435_, v___x_440_);
v___x_442_ = lean_int_ediv(v___y_435_, v___x_440_);
v___x_443_ = lean_int_emod(v___x_442_, v___x_440_);
lean_dec(v___x_442_);
v___x_444_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__14, &l_Std_Time_PlainDateTime_ofWallTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14);
v___x_445_ = lean_int_ediv(v___y_435_, v___x_444_);
lean_dec(v___y_435_);
v___x_446_ = lean_int_emod(v___x_433_, v___x_431_);
lean_dec(v___x_433_);
v___x_447_ = l_Fin_succ___redArg(v___y_437_);
lean_dec(v___y_437_);
v___x_448_ = lean_nat_dec_le(v___x_428_, v___x_447_);
if (v___x_448_ == 0)
{
lean_dec(v___x_447_);
v___y_412_ = v_year_439_;
v___y_413_ = v___x_446_;
v___y_414_ = v___x_445_;
v___y_415_ = v_hmon_438_;
v___y_416_ = v___x_443_;
v___y_417_ = v___y_436_;
v___y_418_ = v___x_441_;
v___y_419_ = v___x_429_;
goto v___jp_411_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_nat_to_int(v___x_447_);
v___y_412_ = v_year_439_;
v___y_413_ = v___x_446_;
v___y_414_ = v___x_445_;
v___y_415_ = v_hmon_438_;
v___y_416_ = v___x_443_;
v___y_417_ = v___y_436_;
v___y_418_ = v___x_441_;
v___y_419_ = v___x_449_;
goto v___jp_411_;
}
}
v___jp_450_:
{
lean_object* v___x_457_; lean_object* v_remDays_458_; lean_object* v___x_459_; lean_object* v_months_460_; lean_object* v___x_461_; lean_object* v_mon_462_; lean_object* v___x_464_; 
v___x_457_ = lean_int_mul(v_remYears_456_, v___x_405_);
v_remDays_458_ = lean_int_sub(v___y_455_, v___x_457_);
lean_dec(v___x_457_);
lean_dec(v___y_455_);
v___x_459_ = lean_unsigned_to_nat(31u);
v_months_460_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__28, &l_Std_Time_PlainDateTime_ofWallTime___closed__28_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28);
v___x_461_ = lean_unsigned_to_nat(0u);
v_mon_462_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__29, &l_Std_Time_PlainDateTime_ofWallTime___closed__29_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v_mon_462_);
lean_ctor_set(v___x_402_, 0, v_remDays_458_);
v___x_464_ = v___x_402_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_remDays_458_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_mon_462_);
v___x_464_ = v_reuseFailAlloc_486_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_year_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_465_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_months_460_, v___x_464_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_fst_466_);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
lean_inc(v_snd_467_);
lean_dec_ref(v___x_465_);
v___x_468_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__30, &l_Std_Time_PlainDateTime_ofWallTime___closed__30_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30);
v___x_469_ = lean_int_add(v___x_468_, v_remYears_456_);
lean_dec(v_remYears_456_);
v___x_470_ = lean_int_mul(v___x_410_, v___y_452_);
lean_dec(v___y_452_);
v___x_471_ = lean_int_add(v___x_469_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_int_mul(v___x_408_, v___y_454_);
lean_dec(v___y_454_);
v___x_473_ = lean_int_add(v___x_471_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_int_mul(v___x_406_, v___y_451_);
lean_dec(v___y_451_);
v_year_475_ = lean_int_add(v___x_473_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_473_);
v___x_476_ = l_Int_toNat(v_fst_466_);
lean_dec(v_fst_466_);
v___x_477_ = lean_nat_mod(v___x_476_, v___x_459_);
lean_dec(v___x_476_);
v___x_478_ = lean_unsigned_to_nat(10u);
v___x_479_ = lean_nat_dec_lt(v___x_478_, v_snd_467_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = lean_nat_add(v_snd_467_, v___x_480_);
lean_dec(v_snd_467_);
v___x_482_ = lean_nat_to_int(v___x_481_);
v___y_435_ = v___y_453_;
v___y_436_ = v___x_461_;
v___y_437_ = v___x_477_;
v_hmon_438_ = v___x_482_;
v_year_439_ = v_year_475_;
goto v___jp_434_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_int_add(v_year_475_, v___x_429_);
lean_dec(v_year_475_);
v___x_484_ = lean_nat_sub(v_snd_467_, v___x_478_);
lean_dec(v_snd_467_);
v___x_485_ = lean_nat_to_int(v___x_484_);
v___y_435_ = v___y_453_;
v___y_436_ = v___x_461_;
v___y_437_ = v___x_477_;
v_hmon_438_ = v___x_485_;
v_year_439_ = v___x_483_;
goto v___jp_434_;
}
}
}
v___jp_487_:
{
lean_object* v___x_493_; lean_object* v_remDays_494_; lean_object* v_remYears_495_; uint8_t v___x_496_; 
v___x_493_ = lean_int_mul(v_quadrennialCycles_492_, v_daysPer4Y_430_);
v_remDays_494_ = lean_int_sub(v___y_491_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___y_491_);
v_remYears_495_ = lean_int_ediv(v_remDays_494_, v___x_405_);
v___x_496_ = lean_int_dec_eq(v_remYears_495_, v___x_410_);
if (v___x_496_ == 0)
{
v___y_451_ = v___y_488_;
v___y_452_ = v_quadrennialCycles_492_;
v___y_453_ = v___y_489_;
v___y_454_ = v___y_490_;
v___y_455_ = v_remDays_494_;
v_remYears_456_ = v_remYears_495_;
goto v___jp_450_;
}
else
{
lean_object* v_remYears_497_; 
v_remYears_497_ = lean_int_sub(v_remYears_495_, v___x_429_);
lean_dec(v_remYears_495_);
v___y_451_ = v___y_488_;
v___y_452_ = v_quadrennialCycles_492_;
v___y_453_ = v___y_489_;
v___y_454_ = v___y_490_;
v___y_455_ = v_remDays_494_;
v_remYears_456_ = v_remYears_497_;
goto v___jp_450_;
}
}
v___jp_498_:
{
lean_object* v___x_503_; lean_object* v_remDays_504_; lean_object* v_quadrennialCycles_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_503_ = lean_int_mul(v_centenialCycles_502_, v_daysPer100Y_409_);
v_remDays_504_ = lean_int_sub(v___y_501_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___y_501_);
v_quadrennialCycles_505_ = lean_int_ediv(v_remDays_504_, v_daysPer4Y_430_);
v___x_506_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__31, &l_Std_Time_PlainDateTime_ofWallTime___closed__31_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31);
v___x_507_ = lean_int_dec_eq(v_quadrennialCycles_505_, v___x_506_);
if (v___x_507_ == 0)
{
v___y_488_ = v___y_499_;
v___y_489_ = v___y_500_;
v___y_490_ = v_centenialCycles_502_;
v___y_491_ = v_remDays_504_;
v_quadrennialCycles_492_ = v_quadrennialCycles_505_;
goto v___jp_487_;
}
else
{
lean_object* v_quadrennialCycles_508_; 
v_quadrennialCycles_508_ = lean_int_sub(v_quadrennialCycles_505_, v___x_429_);
lean_dec(v_quadrennialCycles_505_);
v___y_488_ = v___y_499_;
v___y_489_ = v___y_500_;
v___y_490_ = v_centenialCycles_502_;
v___y_491_ = v_remDays_504_;
v_quadrennialCycles_492_ = v_quadrennialCycles_508_;
goto v___jp_487_;
}
}
v___jp_509_:
{
lean_object* v_centenialCycles_513_; uint8_t v___x_514_; 
v_centenialCycles_513_ = lean_int_ediv(v_remDays_512_, v_daysPer100Y_409_);
v___x_514_ = lean_int_dec_eq(v_centenialCycles_513_, v___x_410_);
if (v___x_514_ == 0)
{
v___y_499_ = v_quadracentennialCycles_511_;
v___y_500_ = v___y_510_;
v___y_501_ = v_remDays_512_;
v_centenialCycles_502_ = v_centenialCycles_513_;
goto v___jp_498_;
}
else
{
lean_object* v_centenialCycles_515_; 
v_centenialCycles_515_ = lean_int_sub(v_centenialCycles_513_, v___x_429_);
lean_dec(v_centenialCycles_513_);
v___y_499_ = v_quadracentennialCycles_511_;
v___y_500_ = v___y_510_;
v___y_501_ = v_remDays_512_;
v_centenialCycles_502_ = v_centenialCycles_515_;
goto v___jp_498_;
}
}
v___jp_516_:
{
lean_object* v_quadracentennialCycles_519_; lean_object* v_remDays_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_quadracentennialCycles_519_ = lean_int_ediv(v_snd_518_, v_daysPer400Y_407_);
v_remDays_520_ = lean_int_emod(v_snd_518_, v_daysPer400Y_407_);
lean_dec(v_snd_518_);
v___x_521_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_522_ = lean_int_dec_lt(v_remDays_520_, v___x_521_);
if (v___x_522_ == 0)
{
v___y_510_ = v_fst_517_;
v_quadracentennialCycles_511_ = v_quadracentennialCycles_519_;
v_remDays_512_ = v_remDays_520_;
goto v___jp_509_;
}
else
{
lean_object* v_remDays_523_; lean_object* v_quadracentennialCycles_524_; 
v_remDays_523_ = lean_int_add(v_remDays_520_, v_daysPer400Y_407_);
lean_dec(v_remDays_520_);
v_quadracentennialCycles_524_ = lean_int_sub(v_quadracentennialCycles_519_, v___x_429_);
lean_dec(v_quadracentennialCycles_519_);
v___y_510_ = v_fst_517_;
v_quadracentennialCycles_511_ = v_quadracentennialCycles_524_;
v_remDays_512_ = v_remDays_523_;
goto v___jp_509_;
}
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v_boundedDaysSinceEpoch_528_; lean_object* v_rawDays_529_; lean_object* v_h_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_527_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v_boundedDaysSinceEpoch_528_ = lean_int_div(v_snd_526_, v___x_527_);
v_rawDays_529_ = lean_int_sub(v_boundedDaysSinceEpoch_528_, v___x_404_);
lean_dec(v_boundedDaysSinceEpoch_528_);
v_h_530_ = lean_int_mod(v_snd_526_, v___x_527_);
lean_dec(v_snd_526_);
v___x_531_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__32, &l_Std_Time_PlainDateTime_ofWallTime___closed__32_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__32);
v___x_532_ = lean_int_dec_le(v_h_530_, v___x_531_);
if (v___x_532_ == 0)
{
v_fst_517_ = v_h_530_;
v_snd_518_ = v_rawDays_529_;
goto v___jp_516_;
}
else
{
lean_object* v___x_533_; lean_object* v_rawDays_534_; 
v___x_533_ = lean_int_add(v_h_530_, v___x_527_);
lean_dec(v_h_530_);
v_rawDays_534_ = lean_int_sub(v_rawDays_529_, v___x_429_);
lean_dec(v_rawDays_529_);
v_fst_517_ = v___x_533_;
v_snd_518_ = v_rawDays_534_;
goto v___jp_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(lean_object* v_as_541_, lean_object* v_as_x27_542_, lean_object* v_b_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_as_x27_542_, v_b_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(lean_object* v_as_546_, lean_object* v_as_x27_547_, lean_object* v_b_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(v_as_546_, v_as_x27_547_, v_b_548_, v_a_549_);
lean_dec(v_as_x27_547_);
lean_dec(v_as_546_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toEpochDay(lean_object* v_pdt_551_){
_start:
{
lean_object* v_date_552_; lean_object* v___x_553_; 
v_date_552_ = lean_ctor_get(v_pdt_551_, 0);
lean_inc_ref(v_date_552_);
lean_dec_ref(v_pdt_551_);
v___x_553_ = l_Std_Time_PlainDate_toEpochDay(v_date_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay(lean_object* v_days_554_, lean_object* v_time_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = l_Std_Time_PlainDate_ofEpochDay(v_days_554_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v_time_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofEpochDay___boxed(lean_object* v_days_558_, lean_object* v_time_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_558_, v_time_559_);
lean_dec(v_days_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object* v_dt_561_, uint8_t v_desiredWeekday_562_){
_start:
{
lean_object* v_date_563_; lean_object* v_time_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_572_; 
v_date_563_ = lean_ctor_get(v_dt_561_, 0);
v_time_564_ = lean_ctor_get(v_dt_561_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_dt_561_);
if (v_isSharedCheck_572_ == 0)
{
v___x_566_ = v_dt_561_;
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_time_564_);
lean_inc(v_date_563_);
lean_dec(v_dt_561_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Std_Time_PlainDate_withWeekday(v_date_563_, v_desiredWeekday_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_time_564_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withWeekday___boxed(lean_object* v_dt_573_, lean_object* v_desiredWeekday_574_){
_start:
{
uint8_t v_desiredWeekday_boxed_575_; lean_object* v_res_576_; 
v_desiredWeekday_boxed_575_ = lean_unbox(v_desiredWeekday_574_);
v_res_576_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_573_, v_desiredWeekday_boxed_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysClip(lean_object* v_dt_577_, lean_object* v_days_578_){
_start:
{
lean_object* v_date_579_; lean_object* v_time_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_620_; 
v_date_579_ = lean_ctor_get(v_dt_577_, 0);
v_time_580_ = lean_ctor_get(v_dt_577_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_dt_577_);
if (v_isSharedCheck_620_ == 0)
{
v___x_582_ = v_dt_577_;
v_isShared_583_ = v_isSharedCheck_620_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_time_580_);
lean_inc(v_date_579_);
lean_dec(v_dt_577_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_620_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_year_584_; lean_object* v_month_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_618_; 
v_year_584_ = lean_ctor_get(v_date_579_, 0);
v_month_585_ = lean_ctor_get(v_date_579_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_date_579_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_date_579_, 2);
lean_dec(v_unused_619_);
v___x_587_ = v_date_579_;
v_isShared_588_ = v_isSharedCheck_618_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_month_585_);
lean_inc(v_year_584_);
lean_dec(v_date_579_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_618_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v___y_590_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; uint8_t v___y_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_605_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_606_ = lean_int_mod(v_year_584_, v___x_605_);
v___x_607_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_608_ = lean_int_dec_eq(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_611_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_612_ = lean_int_mod(v_year_584_, v___x_611_);
v___x_613_ = lean_int_dec_eq(v___x_612_, v___x_607_);
lean_dec(v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = 1;
v___y_610_ = v___x_614_;
goto v___jp_609_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_616_ = lean_int_mod(v_year_584_, v___x_615_);
v___x_617_ = lean_int_dec_eq(v___x_616_, v___x_607_);
lean_dec(v___x_616_);
v___y_610_ = v___x_617_;
goto v___jp_609_;
}
v___jp_589_:
{
lean_object* v_max_591_; uint8_t v___x_592_; 
v_max_591_ = l_Std_Time_Month_Ordinal_days(v___y_590_, v_month_585_);
v___x_592_ = lean_int_dec_lt(v_max_591_, v_days_578_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v_max_591_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v_days_578_);
v___x_594_ = v___x_587_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_year_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_month_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_days_578_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_594_);
v___x_596_ = v___x_582_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_time_580_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v___x_600_; 
lean_dec(v_days_578_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v_max_591_);
v___x_600_ = v___x_587_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_year_584_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_month_585_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_max_591_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_600_);
v___x_602_ = v___x_582_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_time_580_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
v___jp_609_:
{
if (v___x_608_ == 0)
{
v___y_590_ = v___x_608_;
goto v___jp_589_;
}
else
{
v___y_590_ = v___y_610_;
goto v___jp_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver(lean_object* v_dt_621_, lean_object* v_days_622_){
_start:
{
lean_object* v_date_623_; lean_object* v_time_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_634_; 
v_date_623_ = lean_ctor_get(v_dt_621_, 0);
v_time_624_ = lean_ctor_get(v_dt_621_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_dt_621_);
if (v_isSharedCheck_634_ == 0)
{
v___x_626_ = v_dt_621_;
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_time_624_);
lean_inc(v_date_623_);
lean_dec(v_dt_621_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_year_628_; lean_object* v_month_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v_year_628_ = lean_ctor_get(v_date_623_, 0);
lean_inc(v_year_628_);
v_month_629_ = lean_ctor_get(v_date_623_, 1);
lean_inc(v_month_629_);
lean_dec_ref(v_date_623_);
v___x_630_ = l_Std_Time_PlainDate_rollOver(v_year_628_, v_month_629_, v_days_622_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_630_);
v___x_632_ = v___x_626_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_time_624_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withDaysRollOver___boxed(lean_object* v_dt_635_, lean_object* v_days_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_635_, v_days_636_);
lean_dec(v_days_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthClip(lean_object* v_dt_638_, lean_object* v_month_639_){
_start:
{
lean_object* v_date_640_; lean_object* v_time_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_681_; 
v_date_640_ = lean_ctor_get(v_dt_638_, 0);
v_time_641_ = lean_ctor_get(v_dt_638_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_dt_638_);
if (v_isSharedCheck_681_ == 0)
{
v___x_643_ = v_dt_638_;
v_isShared_644_ = v_isSharedCheck_681_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_time_641_);
lean_inc(v_date_640_);
lean_dec(v_dt_638_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_681_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_year_645_; lean_object* v_day_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_679_; 
v_year_645_ = lean_ctor_get(v_date_640_, 0);
v_day_646_ = lean_ctor_get(v_date_640_, 2);
v_isSharedCheck_679_ = !lean_is_exclusive(v_date_640_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v_date_640_, 1);
lean_dec(v_unused_680_);
v___x_648_ = v_date_640_;
v_isShared_649_ = v_isSharedCheck_679_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_day_646_);
lean_inc(v_year_645_);
lean_dec(v_date_640_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_679_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___y_651_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; uint8_t v___y_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_666_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_667_ = lean_int_mod(v_year_645_, v___x_666_);
v___x_668_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_669_ = lean_int_dec_eq(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
v___x_672_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_673_ = lean_int_mod(v_year_645_, v___x_672_);
v___x_674_ = lean_int_dec_eq(v___x_673_, v___x_668_);
lean_dec(v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
v___x_675_ = 1;
v___y_671_ = v___x_675_;
goto v___jp_670_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_677_ = lean_int_mod(v_year_645_, v___x_676_);
v___x_678_ = lean_int_dec_eq(v___x_677_, v___x_668_);
lean_dec(v___x_677_);
v___y_671_ = v___x_678_;
goto v___jp_670_;
}
v___jp_650_:
{
lean_object* v_max_652_; uint8_t v___x_653_; 
v_max_652_ = l_Std_Time_Month_Ordinal_days(v___y_651_, v_month_639_);
v___x_653_ = lean_int_dec_lt(v_max_652_, v_day_646_);
if (v___x_653_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v_max_652_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_month_639_);
v___x_655_ = v___x_648_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_year_645_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_month_639_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_day_646_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_655_);
v___x_657_ = v___x_643_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_time_641_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v___x_661_; 
lean_dec(v_day_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v_max_652_);
lean_ctor_set(v___x_648_, 1, v_month_639_);
v___x_661_ = v___x_648_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_year_645_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_month_639_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_max_652_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_661_);
v___x_663_ = v___x_643_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_time_641_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
v___jp_670_:
{
if (v___x_669_ == 0)
{
v___y_651_ = v___x_669_;
goto v___jp_650_;
}
else
{
v___y_651_ = v___y_671_;
goto v___jp_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMonthRollOver(lean_object* v_dt_682_, lean_object* v_month_683_){
_start:
{
lean_object* v_date_684_; lean_object* v_time_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
v_date_684_ = lean_ctor_get(v_dt_682_, 0);
v_time_685_ = lean_ctor_get(v_dt_682_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_dt_682_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v_dt_682_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_time_685_);
lean_inc(v_date_684_);
lean_dec(v_dt_682_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_year_689_; lean_object* v_day_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_year_689_ = lean_ctor_get(v_date_684_, 0);
lean_inc(v_year_689_);
v_day_690_ = lean_ctor_get(v_date_684_, 2);
lean_inc(v_day_690_);
lean_dec_ref(v_date_684_);
v___x_691_ = l_Std_Time_PlainDate_rollOver(v_year_689_, v_month_683_, v_day_690_);
lean_dec(v_day_690_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_691_);
v___x_693_ = v___x_687_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_time_685_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearClip(lean_object* v_dt_696_, lean_object* v_year_697_){
_start:
{
lean_object* v_date_698_; lean_object* v_time_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_739_; 
v_date_698_ = lean_ctor_get(v_dt_696_, 0);
v_time_699_ = lean_ctor_get(v_dt_696_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_dt_696_);
if (v_isSharedCheck_739_ == 0)
{
v___x_701_ = v_dt_696_;
v_isShared_702_ = v_isSharedCheck_739_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_time_699_);
lean_inc(v_date_698_);
lean_dec(v_dt_696_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_739_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_month_703_; lean_object* v_day_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_737_; 
v_month_703_ = lean_ctor_get(v_date_698_, 1);
v_day_704_ = lean_ctor_get(v_date_698_, 2);
v_isSharedCheck_737_ = !lean_is_exclusive(v_date_698_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_date_698_, 0);
lean_dec(v_unused_738_);
v___x_706_ = v_date_698_;
v_isShared_707_ = v_isSharedCheck_737_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_day_704_);
lean_inc(v_month_703_);
lean_dec(v_date_698_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_737_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
uint8_t v___y_709_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; uint8_t v___y_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_724_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_725_ = lean_int_mod(v_year_697_, v___x_724_);
v___x_726_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_727_ = lean_int_dec_eq(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
v___x_730_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_731_ = lean_int_mod(v_year_697_, v___x_730_);
v___x_732_ = lean_int_dec_eq(v___x_731_, v___x_726_);
lean_dec(v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = 1;
v___y_729_ = v___x_733_;
goto v___jp_728_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_735_ = lean_int_mod(v_year_697_, v___x_734_);
v___x_736_ = lean_int_dec_eq(v___x_735_, v___x_726_);
lean_dec(v___x_735_);
v___y_729_ = v___x_736_;
goto v___jp_728_;
}
v___jp_708_:
{
lean_object* v_max_710_; uint8_t v___x_711_; 
v_max_710_ = l_Std_Time_Month_Ordinal_days(v___y_709_, v_month_703_);
v___x_711_ = lean_int_dec_lt(v_max_710_, v_day_704_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; 
lean_dec(v_max_710_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v_year_697_);
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_year_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_month_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_day_704_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_713_);
v___x_715_ = v___x_701_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_time_699_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_object* v___x_719_; 
lean_dec(v_day_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 2, v_max_710_);
lean_ctor_set(v___x_706_, 0, v_year_697_);
v___x_719_ = v___x_706_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_year_697_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_month_703_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_max_710_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_719_);
v___x_721_ = v___x_701_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_time_699_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
v___jp_728_:
{
if (v___x_727_ == 0)
{
v___y_709_ = v___x_727_;
goto v___jp_708_;
}
else
{
v___y_709_ = v___y_729_;
goto v___jp_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withYearRollOver(lean_object* v_dt_740_, lean_object* v_year_741_){
_start:
{
lean_object* v_date_742_; lean_object* v_time_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v_date_742_ = lean_ctor_get(v_dt_740_, 0);
v_time_743_ = lean_ctor_get(v_dt_740_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_dt_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_745_ = v_dt_740_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_time_743_);
lean_inc(v_date_742_);
lean_dec(v_dt_740_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_month_747_; lean_object* v_day_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v_month_747_ = lean_ctor_get(v_date_742_, 1);
lean_inc(v_month_747_);
v_day_748_ = lean_ctor_get(v_date_742_, 2);
lean_inc(v_day_748_);
lean_dec_ref(v_date_742_);
v___x_749_ = l_Std_Time_PlainDate_rollOver(v_year_741_, v_month_747_, v_day_748_);
lean_dec(v_day_748_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_time_743_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withHours(lean_object* v_dt_754_, lean_object* v_hour_755_){
_start:
{
lean_object* v_time_756_; lean_object* v_date_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_775_; 
v_time_756_ = lean_ctor_get(v_dt_754_, 1);
v_date_757_ = lean_ctor_get(v_dt_754_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_dt_754_);
if (v_isSharedCheck_775_ == 0)
{
v___x_759_ = v_dt_754_;
v_isShared_760_ = v_isSharedCheck_775_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_time_756_);
lean_inc(v_date_757_);
lean_dec(v_dt_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_775_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_minute_761_; lean_object* v_second_762_; lean_object* v_nanosecond_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_773_; 
v_minute_761_ = lean_ctor_get(v_time_756_, 1);
v_second_762_ = lean_ctor_get(v_time_756_, 2);
v_nanosecond_763_ = lean_ctor_get(v_time_756_, 3);
v_isSharedCheck_773_ = !lean_is_exclusive(v_time_756_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_time_756_, 0);
lean_dec(v_unused_774_);
v___x_765_ = v_time_756_;
v_isShared_766_ = v_isSharedCheck_773_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_nanosecond_763_);
lean_inc(v_second_762_);
lean_inc(v_minute_761_);
lean_dec(v_time_756_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_773_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_hour_755_);
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_hour_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_minute_761_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_second_762_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_nanosecond_763_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_768_);
v___x_770_ = v___x_759_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_date_757_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMinutes(lean_object* v_dt_776_, lean_object* v_minute_777_){
_start:
{
lean_object* v_time_778_; lean_object* v_date_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_797_; 
v_time_778_ = lean_ctor_get(v_dt_776_, 1);
v_date_779_ = lean_ctor_get(v_dt_776_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_dt_776_);
if (v_isSharedCheck_797_ == 0)
{
v___x_781_ = v_dt_776_;
v_isShared_782_ = v_isSharedCheck_797_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_time_778_);
lean_inc(v_date_779_);
lean_dec(v_dt_776_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_797_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_hour_783_; lean_object* v_second_784_; lean_object* v_nanosecond_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_795_; 
v_hour_783_ = lean_ctor_get(v_time_778_, 0);
v_second_784_ = lean_ctor_get(v_time_778_, 2);
v_nanosecond_785_ = lean_ctor_get(v_time_778_, 3);
v_isSharedCheck_795_ = !lean_is_exclusive(v_time_778_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_time_778_, 1);
lean_dec(v_unused_796_);
v___x_787_ = v_time_778_;
v_isShared_788_ = v_isSharedCheck_795_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_nanosecond_785_);
lean_inc(v_second_784_);
lean_inc(v_hour_783_);
lean_dec(v_time_778_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_795_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_minute_777_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_hour_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_minute_777_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_second_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_nanosecond_785_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_790_);
v___x_792_ = v___x_781_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_date_779_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withSeconds(lean_object* v_dt_798_, lean_object* v_second_799_){
_start:
{
lean_object* v_time_800_; lean_object* v_date_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_819_; 
v_time_800_ = lean_ctor_get(v_dt_798_, 1);
v_date_801_ = lean_ctor_get(v_dt_798_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_dt_798_);
if (v_isSharedCheck_819_ == 0)
{
v___x_803_ = v_dt_798_;
v_isShared_804_ = v_isSharedCheck_819_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_time_800_);
lean_inc(v_date_801_);
lean_dec(v_dt_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_819_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_hour_805_; lean_object* v_minute_806_; lean_object* v_nanosecond_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
v_hour_805_ = lean_ctor_get(v_time_800_, 0);
v_minute_806_ = lean_ctor_get(v_time_800_, 1);
v_nanosecond_807_ = lean_ctor_get(v_time_800_, 3);
v_isSharedCheck_817_ = !lean_is_exclusive(v_time_800_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_time_800_, 2);
lean_dec(v_unused_818_);
v___x_809_ = v_time_800_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_nanosecond_807_);
lean_inc(v_minute_806_);
lean_inc(v_hour_805_);
lean_dec(v_time_800_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 2, v_second_799_);
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_hour_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_minute_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_second_799_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_nanosecond_807_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_812_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_date_801_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(1000u);
v___x_821_ = lean_nat_to_int(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_unsigned_to_nat(1000000u);
v___x_823_ = lean_nat_to_int(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds(lean_object* v_dt_824_, lean_object* v_millis_825_){
_start:
{
lean_object* v_time_826_; lean_object* v_date_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_850_; 
v_time_826_ = lean_ctor_get(v_dt_824_, 1);
v_date_827_ = lean_ctor_get(v_dt_824_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_dt_824_);
if (v_isSharedCheck_850_ == 0)
{
v___x_829_ = v_dt_824_;
v_isShared_830_ = v_isSharedCheck_850_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_time_826_);
lean_inc(v_date_827_);
lean_dec(v_dt_824_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_850_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_hour_831_; lean_object* v_minute_832_; lean_object* v_second_833_; lean_object* v_nanosecond_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_849_; 
v_hour_831_ = lean_ctor_get(v_time_826_, 0);
v_minute_832_ = lean_ctor_get(v_time_826_, 1);
v_second_833_ = lean_ctor_get(v_time_826_, 2);
v_nanosecond_834_ = lean_ctor_get(v_time_826_, 3);
v_isSharedCheck_849_ = !lean_is_exclusive(v_time_826_);
if (v_isSharedCheck_849_ == 0)
{
v___x_836_ = v_time_826_;
v_isShared_837_ = v_isSharedCheck_849_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_nanosecond_834_);
lean_inc(v_second_833_);
lean_inc(v_minute_832_);
lean_inc(v_hour_831_);
lean_dec(v_time_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_849_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_838_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__0, &l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0);
v___x_839_ = lean_int_emod(v_nanosecond_834_, v___x_838_);
lean_dec(v_nanosecond_834_);
v___x_840_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_841_ = lean_int_mul(v_millis_825_, v___x_840_);
v___x_842_ = lean_int_add(v___x_841_, v___x_839_);
lean_dec(v___x_839_);
lean_dec(v___x_841_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 3, v___x_842_);
v___x_844_ = v___x_836_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_hour_831_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_minute_832_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_second_833_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v___x_842_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_844_);
v___x_846_ = v___x_829_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_date_827_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withMilliseconds___boxed(lean_object* v_dt_851_, lean_object* v_millis_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_851_, v_millis_852_);
lean_dec(v_millis_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_withNanoseconds(lean_object* v_dt_854_, lean_object* v_nano_855_){
_start:
{
lean_object* v_time_856_; lean_object* v_date_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_875_; 
v_time_856_ = lean_ctor_get(v_dt_854_, 1);
v_date_857_ = lean_ctor_get(v_dt_854_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_dt_854_);
if (v_isSharedCheck_875_ == 0)
{
v___x_859_ = v_dt_854_;
v_isShared_860_ = v_isSharedCheck_875_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_time_856_);
lean_inc(v_date_857_);
lean_dec(v_dt_854_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_875_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_hour_861_; lean_object* v_minute_862_; lean_object* v_second_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_hour_861_ = lean_ctor_get(v_time_856_, 0);
v_minute_862_ = lean_ctor_get(v_time_856_, 1);
v_second_863_ = lean_ctor_get(v_time_856_, 2);
v_isSharedCheck_873_ = !lean_is_exclusive(v_time_856_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_time_856_, 3);
lean_dec(v_unused_874_);
v___x_865_ = v_time_856_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_second_863_);
lean_inc(v_minute_862_);
lean_inc(v_hour_861_);
lean_dec(v_time_856_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 3, v_nano_855_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_hour_861_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_minute_862_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_second_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_nano_855_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_868_);
v___x_870_ = v___x_859_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_date_857_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays(lean_object* v_dt_876_, lean_object* v_days_877_){
_start:
{
lean_object* v_date_878_; lean_object* v_time_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_889_; 
v_date_878_ = lean_ctor_get(v_dt_876_, 0);
v_time_879_ = lean_ctor_get(v_dt_876_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_dt_876_);
if (v_isSharedCheck_889_ == 0)
{
v___x_881_ = v_dt_876_;
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_time_879_);
lean_inc(v_date_878_);
lean_dec(v_dt_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_dateDays_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v_dateDays_883_ = l_Std_Time_PlainDate_toEpochDay(v_date_878_);
v___x_884_ = lean_int_add(v_dateDays_883_, v_days_877_);
lean_dec(v_dateDays_883_);
v___x_885_ = l_Std_Time_PlainDate_ofEpochDay(v___x_884_);
lean_dec(v___x_884_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_885_);
v___x_887_ = v___x_881_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_time_879_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addDays___boxed(lean_object* v_dt_890_, lean_object* v_days_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Time_PlainDateTime_addDays(v_dt_890_, v_days_891_);
lean_dec(v_days_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays(lean_object* v_dt_893_, lean_object* v_days_894_){
_start:
{
lean_object* v_date_895_; lean_object* v_time_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_907_; 
v_date_895_ = lean_ctor_get(v_dt_893_, 0);
v_time_896_ = lean_ctor_get(v_dt_893_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_dt_893_);
if (v_isSharedCheck_907_ == 0)
{
v___x_898_ = v_dt_893_;
v_isShared_899_ = v_isSharedCheck_907_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_time_896_);
lean_inc(v_date_895_);
lean_dec(v_dt_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_907_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v_dateDays_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_900_ = lean_int_neg(v_days_894_);
v_dateDays_901_ = l_Std_Time_PlainDate_toEpochDay(v_date_895_);
v___x_902_ = lean_int_add(v_dateDays_901_, v___x_900_);
lean_dec(v___x_900_);
lean_dec(v_dateDays_901_);
v___x_903_ = l_Std_Time_PlainDate_ofEpochDay(v___x_902_);
lean_dec(v___x_902_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_903_);
v___x_905_ = v___x_898_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_time_896_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subDays___boxed(lean_object* v_dt_908_, lean_object* v_days_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_Time_PlainDateTime_subDays(v_dt_908_, v_days_909_);
lean_dec(v_days_909_);
return v_res_910_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(7u);
v___x_912_ = lean_nat_to_int(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks(lean_object* v_dt_913_, lean_object* v_weeks_914_){
_start:
{
lean_object* v_date_915_; lean_object* v_time_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_928_; 
v_date_915_ = lean_ctor_get(v_dt_913_, 0);
v_time_916_ = lean_ctor_get(v_dt_913_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_dt_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_918_ = v_dt_913_;
v_isShared_919_ = v_isSharedCheck_928_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_time_916_);
lean_inc(v_date_915_);
lean_dec(v_dt_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_928_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_dateDays_920_; lean_object* v___x_921_; lean_object* v_daysToAdd_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v_dateDays_920_ = l_Std_Time_PlainDate_toEpochDay(v_date_915_);
v___x_921_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_922_ = lean_int_mul(v_weeks_914_, v___x_921_);
v___x_923_ = lean_int_add(v_dateDays_920_, v_daysToAdd_922_);
lean_dec(v_daysToAdd_922_);
lean_dec(v_dateDays_920_);
v___x_924_ = l_Std_Time_PlainDate_ofEpochDay(v___x_923_);
lean_dec(v___x_923_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_924_);
v___x_926_ = v___x_918_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_time_916_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addWeeks___boxed(lean_object* v_dt_929_, lean_object* v_weeks_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_929_, v_weeks_930_);
lean_dec(v_weeks_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks(lean_object* v_dt_932_, lean_object* v_weeks_933_){
_start:
{
lean_object* v_date_934_; lean_object* v_time_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_948_; 
v_date_934_ = lean_ctor_get(v_dt_932_, 0);
v_time_935_ = lean_ctor_get(v_dt_932_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_dt_932_);
if (v_isSharedCheck_948_ == 0)
{
v___x_937_ = v_dt_932_;
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_time_935_);
lean_inc(v_date_934_);
lean_dec(v_dt_932_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v_dateDays_940_; lean_object* v___x_941_; lean_object* v_daysToAdd_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_939_ = lean_int_neg(v_weeks_933_);
v_dateDays_940_ = l_Std_Time_PlainDate_toEpochDay(v_date_934_);
v___x_941_ = lean_obj_once(&l_Std_Time_PlainDateTime_addWeeks___closed__0, &l_Std_Time_PlainDateTime_addWeeks___closed__0_once, _init_l_Std_Time_PlainDateTime_addWeeks___closed__0);
v_daysToAdd_942_ = lean_int_mul(v___x_939_, v___x_941_);
lean_dec(v___x_939_);
v___x_943_ = lean_int_add(v_dateDays_940_, v_daysToAdd_942_);
lean_dec(v_daysToAdd_942_);
lean_dec(v_dateDays_940_);
v___x_944_ = l_Std_Time_PlainDate_ofEpochDay(v___x_943_);
lean_dec(v___x_943_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_944_);
v___x_946_ = v___x_937_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_time_935_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subWeeks___boxed(lean_object* v_dt_949_, lean_object* v_weeks_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_949_, v_weeks_950_);
lean_dec(v_weeks_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object* v_dt_952_, lean_object* v_months_953_){
_start:
{
lean_object* v_date_954_; lean_object* v_time_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
v_date_954_ = lean_ctor_get(v_dt_952_, 0);
v_time_955_ = lean_ctor_get(v_dt_952_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_dt_952_);
if (v_isSharedCheck_963_ == 0)
{
v___x_957_ = v_dt_952_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_time_955_);
lean_inc(v_date_954_);
lean_dec(v_dt_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = l_Std_Time_PlainDate_addMonthsClip(v_date_954_, v_months_953_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_time_955_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsClip___boxed(lean_object* v_dt_964_, lean_object* v_months_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_964_, v_months_965_);
lean_dec(v_months_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip(lean_object* v_dt_967_, lean_object* v_months_968_){
_start:
{
lean_object* v_date_969_; lean_object* v_time_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_979_; 
v_date_969_ = lean_ctor_get(v_dt_967_, 0);
v_time_970_ = lean_ctor_get(v_dt_967_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_dt_967_);
if (v_isSharedCheck_979_ == 0)
{
v___x_972_ = v_dt_967_;
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_time_970_);
lean_inc(v_date_969_);
lean_dec(v_dt_967_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = lean_int_neg(v_months_968_);
v___x_975_ = l_Std_Time_PlainDate_addMonthsClip(v_date_969_, v___x_974_);
lean_dec(v___x_974_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_time_970_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsClip___boxed(lean_object* v_dt_980_, lean_object* v_months_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_980_, v_months_981_);
lean_dec(v_months_981_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object* v_dt_983_, lean_object* v_months_984_){
_start:
{
lean_object* v_date_985_; lean_object* v_time_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_date_985_ = lean_ctor_get(v_dt_983_, 0);
v_time_986_ = lean_ctor_get(v_dt_983_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_dt_983_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v_dt_983_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_time_986_);
lean_inc(v_date_985_);
lean_dec(v_dt_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_985_, v_months_984_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_time_986_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(lean_object* v_dt_995_, lean_object* v_months_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_995_, v_months_996_);
lean_dec(v_months_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver(lean_object* v_dt_998_, lean_object* v_months_999_){
_start:
{
lean_object* v_date_1000_; lean_object* v_time_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1010_; 
v_date_1000_ = lean_ctor_get(v_dt_998_, 0);
v_time_1001_ = lean_ctor_get(v_dt_998_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_dt_998_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1003_ = v_dt_998_;
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_time_1001_);
lean_inc(v_date_1000_);
lean_dec(v_dt_998_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1005_ = lean_int_neg(v_months_999_);
v___x_1006_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1000_, v___x_1005_);
lean_dec(v___x_1005_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1006_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_time_1001_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(lean_object* v_dt_1011_, lean_object* v_months_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_1011_, v_months_1012_);
lean_dec(v_months_1012_);
return v_res_1013_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(12u);
v___x_1015_ = lean_nat_to_int(v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver(lean_object* v_dt_1016_, lean_object* v_years_1017_){
_start:
{
lean_object* v_date_1018_; lean_object* v_time_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_date_1018_ = lean_ctor_get(v_dt_1016_, 0);
v_time_1019_ = lean_ctor_get(v_dt_1016_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_dt_1016_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v_dt_1016_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_time_1019_);
lean_inc(v_date_1018_);
lean_dec(v_dt_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1023_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1024_ = lean_int_mul(v_years_1017_, v___x_1023_);
v___x_1025_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1018_, v___x_1024_);
lean_dec(v___x_1024_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1025_);
v___x_1027_ = v___x_1021_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_time_1019_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsRollOver___boxed(lean_object* v_dt_1030_, lean_object* v_years_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_1030_, v_years_1031_);
lean_dec(v_years_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip(lean_object* v_dt_1033_, lean_object* v_years_1034_){
_start:
{
lean_object* v_date_1035_; lean_object* v_time_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1046_; 
v_date_1035_ = lean_ctor_get(v_dt_1033_, 0);
v_time_1036_ = lean_ctor_get(v_dt_1033_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_dt_1033_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1038_ = v_dt_1033_;
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_time_1036_);
lean_inc(v_date_1035_);
lean_dec(v_dt_1033_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1041_ = lean_int_mul(v_years_1034_, v___x_1040_);
v___x_1042_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1035_, v___x_1041_);
lean_dec(v___x_1041_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1042_);
v___x_1044_ = v___x_1038_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_time_1036_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addYearsClip___boxed(lean_object* v_dt_1047_, lean_object* v_years_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_1047_, v_years_1048_);
lean_dec(v_years_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver(lean_object* v_dt_1050_, lean_object* v_years_1051_){
_start:
{
lean_object* v_date_1052_; lean_object* v_time_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1064_; 
v_date_1052_ = lean_ctor_get(v_dt_1050_, 0);
v_time_1053_ = lean_ctor_get(v_dt_1050_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_dt_1050_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1055_ = v_dt_1050_;
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_time_1053_);
lean_inc(v_date_1052_);
lean_dec(v_dt_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1057_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1058_ = lean_int_mul(v_years_1051_, v___x_1057_);
v___x_1059_ = lean_int_neg(v___x_1058_);
lean_dec(v___x_1058_);
v___x_1060_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1052_, v___x_1059_);
lean_dec(v___x_1059_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1060_);
v___x_1062_ = v___x_1055_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_time_1053_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsRollOver___boxed(lean_object* v_dt_1065_, lean_object* v_years_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_1065_, v_years_1066_);
lean_dec(v_years_1066_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip(lean_object* v_dt_1068_, lean_object* v_years_1069_){
_start:
{
lean_object* v_date_1070_; lean_object* v_time_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1082_; 
v_date_1070_ = lean_ctor_get(v_dt_1068_, 0);
v_time_1071_ = lean_ctor_get(v_dt_1068_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_dt_1068_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1073_ = v_dt_1068_;
v_isShared_1074_ = v_isSharedCheck_1082_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_time_1071_);
lean_inc(v_date_1070_);
lean_dec(v_dt_1068_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1082_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1075_ = lean_obj_once(&l_Std_Time_PlainDateTime_addYearsRollOver___closed__0, &l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0);
v___x_1076_ = lean_int_mul(v_years_1069_, v___x_1075_);
v___x_1077_ = lean_int_neg(v___x_1076_);
lean_dec(v___x_1076_);
v___x_1078_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1070_, v___x_1077_);
lean_dec(v___x_1077_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1078_);
v___x_1080_ = v___x_1073_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_time_1071_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subYearsClip___boxed(lean_object* v_dt_1083_, lean_object* v_years_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_1083_, v_years_1084_);
lean_dec(v_years_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds(lean_object* v_dt_1086_, lean_object* v_nanos_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v_second_1089_; lean_object* v_nano_1090_; lean_object* v___x_1091_; lean_object* v_second_1092_; lean_object* v_nano_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1088_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1086_);
v_second_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_second_1089_);
v_nano_1090_ = lean_ctor_get(v___x_1088_, 1);
lean_inc(v_nano_1090_);
lean_dec_ref(v___x_1088_);
v___x_1091_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1087_);
v_second_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_second_1092_);
v_nano_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc(v_nano_1093_);
lean_dec_ref(v___x_1091_);
v___x_1094_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1095_ = lean_int_mul(v_second_1089_, v___x_1094_);
lean_dec(v_second_1089_);
v___x_1096_ = lean_int_add(v___x_1095_, v_nano_1090_);
lean_dec(v_nano_1090_);
lean_dec(v___x_1095_);
v___x_1097_ = lean_int_mul(v_second_1092_, v___x_1094_);
lean_dec(v_second_1092_);
v___x_1098_ = lean_int_add(v___x_1097_, v_nano_1093_);
lean_dec(v_nano_1093_);
lean_dec(v___x_1097_);
v___x_1099_ = lean_int_add(v___x_1096_, v___x_1098_);
lean_dec(v___x_1098_);
lean_dec(v___x_1096_);
v___x_1100_ = l_Std_Time_Duration_ofNanoseconds(v___x_1099_);
lean_dec(v___x_1099_);
v___x_1101_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addNanoseconds___boxed(lean_object* v_dt_1102_, lean_object* v_nanos_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_1102_, v_nanos_1103_);
lean_dec(v_nanos_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds(lean_object* v_dt_1105_, lean_object* v_nanos_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v_second_1108_; lean_object* v_nano_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_second_1112_; lean_object* v_nano_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1107_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1105_);
v_second_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_second_1108_);
v_nano_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_nano_1109_);
lean_dec_ref(v___x_1107_);
v___x_1110_ = lean_int_neg(v_nanos_1106_);
v___x_1111_ = l_Std_Time_Duration_ofNanoseconds(v___x_1110_);
lean_dec(v___x_1110_);
v_second_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_second_1112_);
v_nano_1113_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_nano_1113_);
lean_dec_ref(v___x_1111_);
v___x_1114_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1115_ = lean_int_mul(v_second_1108_, v___x_1114_);
lean_dec(v_second_1108_);
v___x_1116_ = lean_int_add(v___x_1115_, v_nano_1109_);
lean_dec(v_nano_1109_);
lean_dec(v___x_1115_);
v___x_1117_ = lean_int_mul(v_second_1112_, v___x_1114_);
lean_dec(v_second_1112_);
v___x_1118_ = lean_int_add(v___x_1117_, v_nano_1113_);
lean_dec(v_nano_1113_);
lean_dec(v___x_1117_);
v___x_1119_ = lean_int_add(v___x_1116_, v___x_1118_);
lean_dec(v___x_1118_);
lean_dec(v___x_1116_);
v___x_1120_ = l_Std_Time_Duration_ofNanoseconds(v___x_1119_);
lean_dec(v___x_1119_);
v___x_1121_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subNanoseconds___boxed(lean_object* v_dt_1122_, lean_object* v_nanos_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_1122_, v_nanos_1123_);
lean_dec(v_nanos_1123_);
return v_res_1124_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_cstr_to_nat("3600000000000");
v___x_1126_ = lean_nat_to_int(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours(lean_object* v_dt_1127_, lean_object* v_hours_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v_second_1130_; lean_object* v_nano_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_second_1135_; lean_object* v_nano_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1129_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1127_);
v_second_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_second_1130_);
v_nano_1131_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_nano_1131_);
lean_dec_ref(v___x_1129_);
v___x_1132_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1133_ = lean_int_mul(v_hours_1128_, v___x_1132_);
v___x_1134_ = l_Std_Time_Duration_ofNanoseconds(v___x_1133_);
lean_dec(v___x_1133_);
v_second_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_second_1135_);
v_nano_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_nano_1136_);
lean_dec_ref(v___x_1134_);
v___x_1137_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1138_ = lean_int_mul(v_second_1130_, v___x_1137_);
lean_dec(v_second_1130_);
v___x_1139_ = lean_int_add(v___x_1138_, v_nano_1131_);
lean_dec(v_nano_1131_);
lean_dec(v___x_1138_);
v___x_1140_ = lean_int_mul(v_second_1135_, v___x_1137_);
lean_dec(v_second_1135_);
v___x_1141_ = lean_int_add(v___x_1140_, v_nano_1136_);
lean_dec(v_nano_1136_);
lean_dec(v___x_1140_);
v___x_1142_ = lean_int_add(v___x_1139_, v___x_1141_);
lean_dec(v___x_1141_);
lean_dec(v___x_1139_);
v___x_1143_ = l_Std_Time_Duration_ofNanoseconds(v___x_1142_);
lean_dec(v___x_1142_);
v___x_1144_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addHours___boxed(lean_object* v_dt_1145_, lean_object* v_hours_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_Time_PlainDateTime_addHours(v_dt_1145_, v_hours_1146_);
lean_dec(v_hours_1146_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours(lean_object* v_dt_1148_, lean_object* v_hours_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v_second_1151_; lean_object* v_nano_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_second_1157_; lean_object* v_nano_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1150_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1148_);
v_second_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_second_1151_);
v_nano_1152_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_nano_1152_);
lean_dec_ref(v___x_1150_);
v___x_1153_ = lean_int_neg(v_hours_1149_);
v___x_1154_ = lean_obj_once(&l_Std_Time_PlainDateTime_addHours___closed__0, &l_Std_Time_PlainDateTime_addHours___closed__0_once, _init_l_Std_Time_PlainDateTime_addHours___closed__0);
v___x_1155_ = lean_int_mul(v___x_1153_, v___x_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = l_Std_Time_Duration_ofNanoseconds(v___x_1155_);
lean_dec(v___x_1155_);
v_second_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_second_1157_);
v_nano_1158_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_nano_1158_);
lean_dec_ref(v___x_1156_);
v___x_1159_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1160_ = lean_int_mul(v_second_1151_, v___x_1159_);
lean_dec(v_second_1151_);
v___x_1161_ = lean_int_add(v___x_1160_, v_nano_1152_);
lean_dec(v_nano_1152_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_int_mul(v_second_1157_, v___x_1159_);
lean_dec(v_second_1157_);
v___x_1163_ = lean_int_add(v___x_1162_, v_nano_1158_);
lean_dec(v_nano_1158_);
lean_dec(v___x_1162_);
v___x_1164_ = lean_int_add(v___x_1161_, v___x_1163_);
lean_dec(v___x_1163_);
lean_dec(v___x_1161_);
v___x_1165_ = l_Std_Time_Duration_ofNanoseconds(v___x_1164_);
lean_dec(v___x_1164_);
v___x_1166_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subHours___boxed(lean_object* v_dt_1167_, lean_object* v_hours_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_Time_PlainDateTime_subHours(v_dt_1167_, v_hours_1168_);
lean_dec(v_hours_1168_);
return v_res_1169_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_cstr_to_nat("60000000000");
v___x_1171_ = lean_nat_to_int(v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes(lean_object* v_dt_1172_, lean_object* v_minutes_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v_second_1175_; lean_object* v_nano_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_second_1180_; lean_object* v_nano_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1174_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1172_);
v_second_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_second_1175_);
v_nano_1176_ = lean_ctor_get(v___x_1174_, 1);
lean_inc(v_nano_1176_);
lean_dec_ref(v___x_1174_);
v___x_1177_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1178_ = lean_int_mul(v_minutes_1173_, v___x_1177_);
v___x_1179_ = l_Std_Time_Duration_ofNanoseconds(v___x_1178_);
lean_dec(v___x_1178_);
v_second_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_second_1180_);
v_nano_1181_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_nano_1181_);
lean_dec_ref(v___x_1179_);
v___x_1182_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1183_ = lean_int_mul(v_second_1175_, v___x_1182_);
lean_dec(v_second_1175_);
v___x_1184_ = lean_int_add(v___x_1183_, v_nano_1176_);
lean_dec(v_nano_1176_);
lean_dec(v___x_1183_);
v___x_1185_ = lean_int_mul(v_second_1180_, v___x_1182_);
lean_dec(v_second_1180_);
v___x_1186_ = lean_int_add(v___x_1185_, v_nano_1181_);
lean_dec(v_nano_1181_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_int_add(v___x_1184_, v___x_1186_);
lean_dec(v___x_1186_);
lean_dec(v___x_1184_);
v___x_1188_ = l_Std_Time_Duration_ofNanoseconds(v___x_1187_);
lean_dec(v___x_1187_);
v___x_1189_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMinutes___boxed(lean_object* v_dt_1190_, lean_object* v_minutes_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_1190_, v_minutes_1191_);
lean_dec(v_minutes_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes(lean_object* v_dt_1193_, lean_object* v_minutes_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v_second_1196_; lean_object* v_nano_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_second_1202_; lean_object* v_nano_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1195_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1193_);
v_second_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_second_1196_);
v_nano_1197_ = lean_ctor_get(v___x_1195_, 1);
lean_inc(v_nano_1197_);
lean_dec_ref(v___x_1195_);
v___x_1198_ = lean_int_neg(v_minutes_1194_);
v___x_1199_ = lean_obj_once(&l_Std_Time_PlainDateTime_addMinutes___closed__0, &l_Std_Time_PlainDateTime_addMinutes___closed__0_once, _init_l_Std_Time_PlainDateTime_addMinutes___closed__0);
v___x_1200_ = lean_int_mul(v___x_1198_, v___x_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = l_Std_Time_Duration_ofNanoseconds(v___x_1200_);
lean_dec(v___x_1200_);
v_second_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_second_1202_);
v_nano_1203_ = lean_ctor_get(v___x_1201_, 1);
lean_inc(v_nano_1203_);
lean_dec_ref(v___x_1201_);
v___x_1204_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1205_ = lean_int_mul(v_second_1196_, v___x_1204_);
lean_dec(v_second_1196_);
v___x_1206_ = lean_int_add(v___x_1205_, v_nano_1197_);
lean_dec(v_nano_1197_);
lean_dec(v___x_1205_);
v___x_1207_ = lean_int_mul(v_second_1202_, v___x_1204_);
lean_dec(v_second_1202_);
v___x_1208_ = lean_int_add(v___x_1207_, v_nano_1203_);
lean_dec(v_nano_1203_);
lean_dec(v___x_1207_);
v___x_1209_ = lean_int_add(v___x_1206_, v___x_1208_);
lean_dec(v___x_1208_);
lean_dec(v___x_1206_);
v___x_1210_ = l_Std_Time_Duration_ofNanoseconds(v___x_1209_);
lean_dec(v___x_1209_);
v___x_1211_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMinutes___boxed(lean_object* v_dt_1212_, lean_object* v_minutes_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_1212_, v_minutes_1213_);
lean_dec(v_minutes_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds(lean_object* v_dt_1215_, lean_object* v_seconds_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v_second_1218_; lean_object* v_nano_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_second_1223_; lean_object* v_nano_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1217_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1215_);
v_second_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_second_1218_);
v_nano_1219_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_nano_1219_);
lean_dec_ref(v___x_1217_);
v___x_1220_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1221_ = lean_int_mul(v_seconds_1216_, v___x_1220_);
v___x_1222_ = l_Std_Time_Duration_ofNanoseconds(v___x_1221_);
lean_dec(v___x_1221_);
v_second_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_second_1223_);
v_nano_1224_ = lean_ctor_get(v___x_1222_, 1);
lean_inc(v_nano_1224_);
lean_dec_ref(v___x_1222_);
v___x_1225_ = lean_int_mul(v_second_1218_, v___x_1220_);
lean_dec(v_second_1218_);
v___x_1226_ = lean_int_add(v___x_1225_, v_nano_1219_);
lean_dec(v_nano_1219_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_int_mul(v_second_1223_, v___x_1220_);
lean_dec(v_second_1223_);
v___x_1228_ = lean_int_add(v___x_1227_, v_nano_1224_);
lean_dec(v_nano_1224_);
lean_dec(v___x_1227_);
v___x_1229_ = lean_int_add(v___x_1226_, v___x_1228_);
lean_dec(v___x_1228_);
lean_dec(v___x_1226_);
v___x_1230_ = l_Std_Time_Duration_ofNanoseconds(v___x_1229_);
lean_dec(v___x_1229_);
v___x_1231_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addSeconds___boxed(lean_object* v_dt_1232_, lean_object* v_seconds_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_1232_, v_seconds_1233_);
lean_dec(v_seconds_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds(lean_object* v_dt_1235_, lean_object* v_seconds_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v_second_1238_; lean_object* v_nano_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_second_1244_; lean_object* v_nano_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1237_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1235_);
v_second_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_second_1238_);
v_nano_1239_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_nano_1239_);
lean_dec_ref(v___x_1237_);
v___x_1240_ = lean_int_neg(v_seconds_1236_);
v___x_1241_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1242_ = lean_int_mul(v___x_1240_, v___x_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = l_Std_Time_Duration_ofNanoseconds(v___x_1242_);
lean_dec(v___x_1242_);
v_second_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_second_1244_);
v_nano_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_nano_1245_);
lean_dec_ref(v___x_1243_);
v___x_1246_ = lean_int_mul(v_second_1238_, v___x_1241_);
lean_dec(v_second_1238_);
v___x_1247_ = lean_int_add(v___x_1246_, v_nano_1239_);
lean_dec(v_nano_1239_);
lean_dec(v___x_1246_);
v___x_1248_ = lean_int_mul(v_second_1244_, v___x_1241_);
lean_dec(v_second_1244_);
v___x_1249_ = lean_int_add(v___x_1248_, v_nano_1245_);
lean_dec(v_nano_1245_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_int_add(v___x_1247_, v___x_1249_);
lean_dec(v___x_1249_);
lean_dec(v___x_1247_);
v___x_1251_ = l_Std_Time_Duration_ofNanoseconds(v___x_1250_);
lean_dec(v___x_1250_);
v___x_1252_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subSeconds___boxed(lean_object* v_dt_1253_, lean_object* v_seconds_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_1253_, v_seconds_1254_);
lean_dec(v_seconds_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds(lean_object* v_dt_1256_, lean_object* v_milliseconds_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v_second_1259_; lean_object* v_nano_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_second_1264_; lean_object* v_nano_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1258_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1256_);
v_second_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_second_1259_);
v_nano_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_nano_1260_);
lean_dec_ref(v___x_1258_);
v___x_1261_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1262_ = lean_int_mul(v_milliseconds_1257_, v___x_1261_);
v___x_1263_ = l_Std_Time_Duration_ofNanoseconds(v___x_1262_);
lean_dec(v___x_1262_);
v_second_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_second_1264_);
v_nano_1265_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_nano_1265_);
lean_dec_ref(v___x_1263_);
v___x_1266_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1267_ = lean_int_mul(v_second_1259_, v___x_1266_);
lean_dec(v_second_1259_);
v___x_1268_ = lean_int_add(v___x_1267_, v_nano_1260_);
lean_dec(v_nano_1260_);
lean_dec(v___x_1267_);
v___x_1269_ = lean_int_mul(v_second_1264_, v___x_1266_);
lean_dec(v_second_1264_);
v___x_1270_ = lean_int_add(v___x_1269_, v_nano_1265_);
lean_dec(v_nano_1265_);
lean_dec(v___x_1269_);
v___x_1271_ = lean_int_add(v___x_1268_, v___x_1270_);
lean_dec(v___x_1270_);
lean_dec(v___x_1268_);
v___x_1272_ = l_Std_Time_Duration_ofNanoseconds(v___x_1271_);
lean_dec(v___x_1271_);
v___x_1273_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_addMilliseconds___boxed(lean_object* v_dt_1274_, lean_object* v_milliseconds_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_1274_, v_milliseconds_1275_);
lean_dec(v_milliseconds_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds(lean_object* v_dt_1277_, lean_object* v_milliseconds_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v_second_1280_; lean_object* v_nano_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_second_1286_; lean_object* v_nano_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1279_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_1277_);
v_second_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_second_1280_);
v_nano_1281_ = lean_ctor_get(v___x_1279_, 1);
lean_inc(v_nano_1281_);
lean_dec_ref(v___x_1279_);
v___x_1282_ = lean_int_neg(v_milliseconds_1278_);
v___x_1283_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1284_ = lean_int_mul(v___x_1282_, v___x_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = l_Std_Time_Duration_ofNanoseconds(v___x_1284_);
lean_dec(v___x_1284_);
v_second_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_second_1286_);
v_nano_1287_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_nano_1287_);
lean_dec_ref(v___x_1285_);
v___x_1288_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1289_ = lean_int_mul(v_second_1280_, v___x_1288_);
lean_dec(v_second_1280_);
v___x_1290_ = lean_int_add(v___x_1289_, v_nano_1281_);
lean_dec(v_nano_1281_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_int_mul(v_second_1286_, v___x_1288_);
lean_dec(v_second_1286_);
v___x_1292_ = lean_int_add(v___x_1291_, v_nano_1287_);
lean_dec(v_nano_1287_);
lean_dec(v___x_1291_);
v___x_1293_ = lean_int_add(v___x_1290_, v___x_1292_);
lean_dec(v___x_1292_);
lean_dec(v___x_1290_);
v___x_1294_ = l_Std_Time_Duration_ofNanoseconds(v___x_1293_);
lean_dec(v___x_1293_);
v___x_1295_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_subMilliseconds___boxed(lean_object* v_dt_1296_, lean_object* v_milliseconds_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_1296_, v_milliseconds_1297_);
lean_dec(v_milliseconds_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year(lean_object* v_dt_1299_){
_start:
{
lean_object* v_date_1300_; lean_object* v_year_1301_; 
v_date_1300_ = lean_ctor_get(v_dt_1299_, 0);
v_year_1301_ = lean_ctor_get(v_date_1300_, 0);
lean_inc(v_year_1301_);
return v_year_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_year___boxed(lean_object* v_dt_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_Time_PlainDateTime_year(v_dt_1302_);
lean_dec_ref(v_dt_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month(lean_object* v_dt_1304_){
_start:
{
lean_object* v_date_1305_; lean_object* v_month_1306_; 
v_date_1305_ = lean_ctor_get(v_dt_1304_, 0);
v_month_1306_ = lean_ctor_get(v_date_1305_, 1);
lean_inc(v_month_1306_);
return v_month_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_month___boxed(lean_object* v_dt_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_Time_PlainDateTime_month(v_dt_1307_);
lean_dec_ref(v_dt_1307_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day(lean_object* v_dt_1309_){
_start:
{
lean_object* v_date_1310_; lean_object* v_day_1311_; 
v_date_1310_ = lean_ctor_get(v_dt_1309_, 0);
v_day_1311_ = lean_ctor_get(v_date_1310_, 2);
lean_inc(v_day_1311_);
return v_day_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_day___boxed(lean_object* v_dt_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_Time_PlainDateTime_day(v_dt_1312_);
lean_dec_ref(v_dt_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_weekday(lean_object* v_dt_1314_){
_start:
{
lean_object* v_date_1315_; uint8_t v___x_1316_; 
v_date_1315_ = lean_ctor_get(v_dt_1314_, 0);
lean_inc_ref(v_date_1315_);
lean_dec_ref(v_dt_1314_);
v___x_1316_ = l_Std_Time_PlainDate_weekday(v_date_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekday___boxed(lean_object* v_dt_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Std_Time_PlainDateTime_weekday(v_dt_1317_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour(lean_object* v_dt_1320_){
_start:
{
lean_object* v_time_1321_; lean_object* v_hour_1322_; 
v_time_1321_ = lean_ctor_get(v_dt_1320_, 1);
v_hour_1322_ = lean_ctor_get(v_time_1321_, 0);
lean_inc(v_hour_1322_);
return v_hour_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_hour___boxed(lean_object* v_dt_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_Time_PlainDateTime_hour(v_dt_1323_);
lean_dec_ref(v_dt_1323_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute(lean_object* v_dt_1325_){
_start:
{
lean_object* v_time_1326_; lean_object* v_minute_1327_; 
v_time_1326_ = lean_ctor_get(v_dt_1325_, 1);
v_minute_1327_ = lean_ctor_get(v_time_1326_, 1);
lean_inc(v_minute_1327_);
return v_minute_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_minute___boxed(lean_object* v_dt_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_Time_PlainDateTime_minute(v_dt_1328_);
lean_dec_ref(v_dt_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond(lean_object* v_dt_1330_){
_start:
{
lean_object* v_time_1331_; lean_object* v_nanosecond_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_time_1331_ = lean_ctor_get(v_dt_1330_, 1);
v_nanosecond_1332_ = lean_ctor_get(v_time_1331_, 3);
v___x_1333_ = lean_obj_once(&l_Std_Time_PlainDateTime_withMilliseconds___closed__1, &l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once, _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1);
v___x_1334_ = lean_int_ediv(v_nanosecond_1332_, v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_millisecond___boxed(lean_object* v_dt_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_Time_PlainDateTime_millisecond(v_dt_1335_);
lean_dec_ref(v_dt_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second(lean_object* v_dt_1337_){
_start:
{
lean_object* v_time_1338_; lean_object* v_second_1339_; 
v_time_1338_ = lean_ctor_get(v_dt_1337_, 1);
v_second_1339_ = lean_ctor_get(v_time_1338_, 2);
lean_inc(v_second_1339_);
return v_second_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_second___boxed(lean_object* v_dt_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_Time_PlainDateTime_second(v_dt_1340_);
lean_dec_ref(v_dt_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond(lean_object* v_dt_1342_){
_start:
{
lean_object* v_time_1343_; lean_object* v_nanosecond_1344_; 
v_time_1343_ = lean_ctor_get(v_dt_1342_, 1);
v_nanosecond_1344_ = lean_ctor_get(v_time_1343_, 3);
lean_inc(v_nanosecond_1344_);
return v_nanosecond_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_nanosecond___boxed(lean_object* v_dt_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_1345_);
lean_dec_ref(v_dt_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_era(lean_object* v_date_1347_){
_start:
{
lean_object* v_date_1348_; lean_object* v_year_1349_; uint8_t v___x_1350_; 
v_date_1348_ = lean_ctor_get(v_date_1347_, 0);
v_year_1349_ = lean_ctor_get(v_date_1348_, 0);
v___x_1350_ = l_Std_Time_Year_Offset_era(v_year_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_era___boxed(lean_object* v_date_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Std_Time_PlainDateTime_era(v_date_1351_);
lean_dec_ref(v_date_1351_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDateTime_inLeapYear(lean_object* v_date_1354_){
_start:
{
lean_object* v_date_1355_; lean_object* v_year_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_date_1355_ = lean_ctor_get(v_date_1354_, 0);
v_year_1356_ = lean_ctor_get(v_date_1355_, 0);
v___x_1357_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1358_ = lean_int_mod(v_year_1356_, v___x_1357_);
v___x_1359_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1360_ = lean_int_dec_eq(v___x_1358_, v___x_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1362_ = lean_int_mod(v_year_1356_, v___x_1361_);
v___x_1363_ = lean_int_dec_eq(v___x_1362_, v___x_1359_);
lean_dec(v___x_1362_);
if (v___x_1363_ == 0)
{
return v___x_1360_;
}
else
{
if (v___x_1360_ == 0)
{
return v___x_1360_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1365_ = lean_int_mod(v_year_1356_, v___x_1364_);
v___x_1366_ = lean_int_dec_eq(v___x_1365_, v___x_1359_);
lean_dec(v___x_1365_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_inLeapYear___boxed(lean_object* v_date_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_1367_);
lean_dec_ref(v_date_1367_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear(lean_object* v_date_1370_, uint8_t v_firstDay_1371_, lean_object* v_minDays_1372_){
_start:
{
lean_object* v_date_1373_; lean_object* v___x_1374_; 
v_date_1373_ = lean_ctor_get(v_date_1370_, 0);
lean_inc_ref(v_date_1373_);
lean_dec_ref(v_date_1370_);
v___x_1374_ = l_Std_Time_PlainDate_weekOfYear(v_date_1373_, v_firstDay_1371_, v_minDays_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfYear___boxed(lean_object* v_date_1375_, lean_object* v_firstDay_1376_, lean_object* v_minDays_1377_){
_start:
{
uint8_t v_firstDay_boxed_1378_; lean_object* v_res_1379_; 
v_firstDay_boxed_1378_ = lean_unbox(v_firstDay_1376_);
v_res_1379_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_1375_, v_firstDay_boxed_1378_, v_minDays_1377_);
lean_dec(v_minDays_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear(lean_object* v_date_1380_, uint8_t v_firstDay_1381_, lean_object* v_minDays_1382_){
_start:
{
lean_object* v_date_1383_; lean_object* v___x_1384_; 
v_date_1383_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1383_);
lean_dec_ref(v_date_1380_);
v___x_1384_ = l_Std_Time_PlainDate_weekYear(v_date_1383_, v_firstDay_1381_, v_minDays_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekYear___boxed(lean_object* v_date_1385_, lean_object* v_firstDay_1386_, lean_object* v_minDays_1387_){
_start:
{
uint8_t v_firstDay_boxed_1388_; lean_object* v_res_1389_; 
v_firstDay_boxed_1388_ = lean_unbox(v_firstDay_1386_);
v_res_1389_ = l_Std_Time_PlainDateTime_weekYear(v_date_1385_, v_firstDay_boxed_1388_, v_minDays_1387_);
lean_dec(v_minDays_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object* v_date_1390_){
_start:
{
lean_object* v_date_1391_; lean_object* v___x_1392_; 
v_date_1391_ = lean_ctor_get(v_date_1390_, 0);
v___x_1392_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1393_);
lean_dec_ref(v_date_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object* v_date_1395_, uint8_t v_firstDay_1396_){
_start:
{
lean_object* v_date_1397_; lean_object* v___x_1398_; 
v_date_1397_ = lean_ctor_get(v_date_1395_, 0);
lean_inc_ref(v_date_1397_);
lean_dec_ref(v_date_1395_);
v___x_1398_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1397_, v_firstDay_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_weekOfMonth___boxed(lean_object* v_date_1399_, lean_object* v_firstDay_1400_){
_start:
{
uint8_t v_firstDay_boxed_1401_; lean_object* v_res_1402_; 
v_firstDay_boxed_1401_ = lean_unbox(v_firstDay_1400_);
v_res_1402_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1399_, v_firstDay_boxed_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_dayOfYear(lean_object* v_date_1403_){
_start:
{
lean_object* v_date_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1430_; 
v_date_1404_ = lean_ctor_get(v_date_1403_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_date_1403_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v_date_1403_, 1);
lean_dec(v_unused_1431_);
v___x_1406_ = v_date_1403_;
v_isShared_1407_ = v_isSharedCheck_1430_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_date_1404_);
lean_dec(v_date_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1430_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_year_1408_; lean_object* v_month_1409_; lean_object* v_day_1410_; uint8_t v___y_1412_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; uint8_t v___y_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_year_1408_ = lean_ctor_get(v_date_1404_, 0);
lean_inc(v_year_1408_);
v_month_1409_ = lean_ctor_get(v_date_1404_, 1);
lean_inc(v_month_1409_);
v_day_1410_ = lean_ctor_get(v_date_1404_, 2);
lean_inc(v_day_1410_);
lean_dec_ref(v_date_1404_);
v___x_1417_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__10, &l_Std_Time_PlainDateTime_ofWallTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10);
v___x_1418_ = lean_int_mod(v_year_1408_, v___x_1417_);
v___x_1419_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1420_ = lean_int_dec_eq(v___x_1418_, v___x_1419_);
lean_dec(v___x_1418_);
v___x_1423_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__6, &l_Std_Time_PlainDateTime_ofWallTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6);
v___x_1424_ = lean_int_mod(v_year_1408_, v___x_1423_);
v___x_1425_ = lean_int_dec_eq(v___x_1424_, v___x_1419_);
lean_dec(v___x_1424_);
if (v___x_1425_ == 0)
{
uint8_t v___x_1426_; 
lean_dec(v_year_1408_);
v___x_1426_ = 1;
v___y_1422_ = v___x_1426_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_obj_once(&l_Std_Time_PlainDateTime_ofWallTime___closed__2, &l_Std_Time_PlainDateTime_ofWallTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2);
v___x_1428_ = lean_int_mod(v_year_1408_, v___x_1427_);
lean_dec(v_year_1408_);
v___x_1429_ = lean_int_dec_eq(v___x_1428_, v___x_1419_);
lean_dec(v___x_1428_);
v___y_1422_ = v___x_1429_;
goto v___jp_1421_;
}
v___jp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_day_1410_);
lean_ctor_set(v___x_1406_, 0, v_month_1409_);
v___x_1414_ = v___x_1406_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_month_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_day_1410_);
v___x_1414_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Std_Time_ValidDate_dayOfYear(v___y_1412_, v___x_1414_);
lean_dec_ref(v___x_1414_);
return v___x_1415_;
}
}
v___jp_1421_:
{
if (v___x_1420_ == 0)
{
v___y_1412_ = v___x_1420_;
goto v___jp_1411_;
}
else
{
v___y_1412_ = v___y_1422_;
goto v___jp_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter(lean_object* v_date_1432_){
_start:
{
lean_object* v_date_1433_; lean_object* v___x_1434_; 
v_date_1433_ = lean_ctor_get(v_date_1432_, 0);
v___x_1434_ = l_Std_Time_PlainDate_quarter(v_date_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_quarter___boxed(lean_object* v_date_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Std_Time_PlainDateTime_quarter(v_date_1435_);
lean_dec_ref(v_date_1435_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atTime(lean_object* v_date_1437_, lean_object* v_time_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_date_1437_);
lean_ctor_set(v___x_1439_, 1, v_time_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_atDate(lean_object* v_time_1440_, lean_object* v_date_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_date_1441_);
lean_ctor_set(v___x_1442_, 1, v_time_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0(lean_object* v_x_1471_, lean_object* v_y_1472_){
_start:
{
lean_object* v_second_1473_; lean_object* v_nano_1474_; lean_object* v___x_1475_; lean_object* v_second_1476_; lean_object* v_nano_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_nanos_1480_; lean_object* v___x_1481_; lean_object* v_second_1482_; lean_object* v_nano_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_second_1473_ = lean_ctor_get(v_y_1472_, 0);
v_nano_1474_ = lean_ctor_get(v_y_1472_, 1);
v___x_1475_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1471_);
v_second_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_second_1476_);
v_nano_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_nano_1477_);
lean_dec_ref(v___x_1475_);
v___x_1478_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1479_ = lean_int_mul(v_second_1473_, v___x_1478_);
v_nanos_1480_ = lean_int_add(v___x_1479_, v_nano_1474_);
lean_dec(v___x_1479_);
v___x_1481_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1480_);
lean_dec(v_nanos_1480_);
v_second_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_second_1482_);
v_nano_1483_ = lean_ctor_get(v___x_1481_, 1);
lean_inc(v_nano_1483_);
lean_dec_ref(v___x_1481_);
v___x_1484_ = lean_int_mul(v_second_1476_, v___x_1478_);
lean_dec(v_second_1476_);
v___x_1485_ = lean_int_add(v___x_1484_, v_nano_1477_);
lean_dec(v_nano_1477_);
lean_dec(v___x_1484_);
v___x_1486_ = lean_int_mul(v_second_1482_, v___x_1478_);
lean_dec(v_second_1482_);
v___x_1487_ = lean_int_add(v___x_1486_, v_nano_1483_);
lean_dec(v_nano_1483_);
lean_dec(v___x_1486_);
v___x_1488_ = lean_int_add(v___x_1485_, v___x_1487_);
lean_dec(v___x_1487_);
lean_dec(v___x_1485_);
v___x_1489_ = l_Std_Time_Duration_ofNanoseconds(v___x_1488_);
lean_dec(v___x_1488_);
v___x_1490_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1491_, lean_object* v_y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_1491_, v_y_1492_);
lean_dec_ref(v_y_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* v_date_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = l_Std_Time_PlainTime_midnight;
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_date_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* v_pdt_1499_){
_start:
{
lean_object* v_date_1500_; 
v_date_1500_ = lean_ctor_get(v_pdt_1499_, 0);
lean_inc_ref(v_date_1500_);
return v_date_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* v_pdt_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_1501_);
lean_dec_ref(v_pdt_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* v_pdt_1503_){
_start:
{
lean_object* v_time_1504_; 
v_time_1504_ = lean_ctor_get(v_pdt_1503_, 1);
lean_inc_ref(v_time_1504_);
return v_time_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* v_pdt_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_1505_);
lean_dec_ref(v_pdt_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* v_x_1507_, lean_object* v_y_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v_second_1510_; lean_object* v_nano_1511_; lean_object* v___x_1512_; lean_object* v_second_1513_; lean_object* v_nano_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1509_ = l_Std_Time_PlainDateTime_toWallTime(v_y_1508_);
v_second_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_second_1510_);
v_nano_1511_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_nano_1511_);
lean_dec_ref(v___x_1509_);
v___x_1512_ = l_Std_Time_PlainDateTime_toWallTime(v_x_1507_);
v_second_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_second_1513_);
v_nano_1514_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_nano_1514_);
lean_dec_ref(v___x_1512_);
v___x_1515_ = lean_int_neg(v_second_1510_);
lean_dec(v_second_1510_);
v___x_1516_ = lean_int_neg(v_nano_1511_);
lean_dec(v_nano_1511_);
v___x_1517_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1518_ = lean_int_mul(v_second_1513_, v___x_1517_);
lean_dec(v_second_1513_);
v___x_1519_ = lean_int_add(v___x_1518_, v_nano_1514_);
lean_dec(v_nano_1514_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_int_mul(v___x_1515_, v___x_1517_);
lean_dec(v___x_1515_);
v___x_1521_ = lean_int_add(v___x_1520_, v___x_1516_);
lean_dec(v___x_1516_);
lean_dec(v___x_1520_);
v___x_1522_ = lean_int_add(v___x_1519_, v___x_1521_);
lean_dec(v___x_1521_);
lean_dec(v___x_1519_);
v___x_1523_ = l_Std_Time_Duration_ofNanoseconds(v___x_1522_);
lean_dec(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toWallTime(lean_object* v_pd_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1527_ = l_Std_Time_PlainDate_toEpochDay(v_pd_1526_);
v___x_1528_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1529_ = lean_int_mul(v___x_1527_, v___x_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime(lean_object* v_wt_1532_){
_start:
{
lean_object* v_second_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_second_1533_ = lean_ctor_get(v_wt_1532_, 0);
v___x_1534_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1535_ = lean_int_div(v_second_1533_, v___x_1534_);
v___x_1536_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1535_);
lean_dec(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofWallTime___boxed(lean_object* v_wt_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Std_Time_PlainDate_ofWallTime(v_wt_1537_);
lean_dec_ref(v_wt_1537_);
return v_res_1538_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1540_ = lean_int_neg(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* v_x_1541_, lean_object* v_y_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1543_ = l_Std_Time_PlainDate_toEpochDay(v_x_1541_);
v___x_1544_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__0, &l_Std_Time_PlainDateTime_toWallTime___closed__0_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__0);
v___x_1545_ = lean_int_mul(v___x_1543_, v___x_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDateTime_default___closed__0, &l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once, _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0);
v___x_1547_ = l_Std_Time_PlainDate_toEpochDay(v_y_1542_);
v___x_1548_ = lean_int_mul(v___x_1547_, v___x_1544_);
lean_dec(v___x_1547_);
v___x_1549_ = lean_int_neg(v___x_1548_);
lean_dec(v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
v___x_1551_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1552_ = lean_int_mul(v___x_1545_, v___x_1551_);
lean_dec(v___x_1545_);
v___x_1553_ = lean_int_add(v___x_1552_, v___x_1546_);
lean_dec(v___x_1552_);
v___x_1554_ = lean_int_mul(v___x_1549_, v___x_1551_);
lean_dec(v___x_1549_);
v___x_1555_ = lean_int_add(v___x_1554_, v___x_1550_);
lean_dec(v___x_1554_);
v___x_1556_ = lean_int_add(v___x_1553_, v___x_1555_);
lean_dec(v___x_1555_);
lean_dec(v___x_1553_);
v___x_1557_ = l_Std_Time_Duration_ofNanoseconds(v___x_1556_);
lean_dec(v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_atTime(lean_object* v_date_1560_, lean_object* v_time_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_date_1560_);
lean_ctor_set(v___x_1562_, 1, v_time_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime(lean_object* v_pt_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1563_);
v___x_1565_ = l_Std_Time_Duration_ofNanoseconds(v___x_1564_);
lean_dec(v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toWallTime___boxed(lean_object* v_pt_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_Time_PlainTime_toWallTime(v_pt_1566_);
lean_dec_ref(v_pt_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime(lean_object* v_wt_1568_){
_start:
{
lean_object* v_second_1569_; lean_object* v_nano_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v_nanos_1573_; lean_object* v___x_1574_; 
v_second_1569_ = lean_ctor_get(v_wt_1568_, 0);
v_nano_1570_ = lean_ctor_get(v_wt_1568_, 1);
v___x_1571_ = lean_obj_once(&l_Std_Time_PlainDateTime_toWallTime___closed__1, &l_Std_Time_PlainDateTime_toWallTime___closed__1_once, _init_l_Std_Time_PlainDateTime_toWallTime___closed__1);
v___x_1572_ = lean_int_mul(v_second_1569_, v___x_1571_);
v_nanos_1573_ = lean_int_add(v___x_1572_, v_nano_1570_);
lean_dec(v___x_1572_);
v___x_1574_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1573_);
lean_dec(v_nanos_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofWallTime___boxed(lean_object* v_wt_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Std_Time_PlainTime_ofWallTime(v_wt_1575_);
lean_dec_ref(v_wt_1575_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_atDate(lean_object* v_time_1577_, lean_object* v_date_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_date_1578_);
lean_ctor_set(v___x_1579_, 1, v_time_1577_);
return v___x_1579_;
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
